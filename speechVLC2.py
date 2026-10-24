#Author: Aaron M. Leonhard
#Date: 09:21:2025
#Description: Offline desktop music player with optional voice control. Playback is a small C# engine (audio_engine,
#built on NAudio) run by Windows PowerShell, and the GUI is plain tkinter, so the app itself needs no internet. Voice commands are recognised offline by Vosk
#(model in the vosk_model folder, microphone read through PyAudio). The old Google version is kept, commented out, below.
#YouTube songs (+YT in the library, switched on and off in Settings) need internet: they play in a Chrome / Edge / Brave
#window the app opens and controls, since YouTube only lets its own player play them.
#Voice keywords:
#"play <song>" / "song <song>" Starts that song from the library
#"playlist <name>" Starts one of your playlists ("playlist" alone plays User_Music/coolPlaylist.xspf)
#"play <station>" / "radio <station>" Starts a radio station *Requires internet connection
#"stop" Stops playback, "pause" / "resume" pauses and resumes
#"next" / "previous" Changes track, "mute" / "unmute" toggles the sound
#"time" / "date" Says the time or date in the voice log, "rick" gets you rick rolled
#"snow" / "rain" Makes it snow or rain over the window until you say "stop" (these three need Fun ticked in Settings)
#"end" / "exit" Closes the app
#
#Layout of this file: settings and storage helpers, the audio engine host (Player), media keys, drawing helpers,
#the canvas widgets (GlassButton, GlassList...), and finally App, which builds the window and wires everything up.

import base64
import bisect
import collections
import difflib
import io
import json
import math
import os
import queue
import random
import re
import secrets
import shutil
import socket
import ssl
import subprocess
import sys
import threading
import time
import tkinter as tk
import urllib.error
import urllib.request
import webbrowser
import xml.etree.ElementTree as ET
from http.client import HTTPException
from pathlib import Path
from tkinter import colorchooser, filedialog
from tkinter import font as tkfont
from urllib.parse import parse_qs, quote, urlparse, unquote

from PIL import Image, ImageChops, ImageDraw, ImageFilter, ImageOps, ImageTk
from tkinterdnd2 import DND_FILES, TkinterDnD

from translations import LANGUAGES, TRANSLATIONS, formatDate, formatTime

# ---- languages ----------------------------------------------------------------------------------------------------
# The app's words are written in English, and T() swaps them for the chosen language's (translations.py). Widgets
# translate the text they're given themselves, so most code just uses English. Messages with names or numbers in them
# are matched by their pattern ("Playing {}"), and the parts filled in are translated too when they're known words.
# Song, playlist and station names are never translated
LANGUAGE = "en" # set from Settings when the app starts (the installer asks for it)
_patterns = {}

def systemLanguage():
    """The language Windows is set to, when the app speaks it, else English"""
    try:
        import ctypes
        primary = ctypes.windll.kernel32.GetUserDefaultUILanguage() & 0x3FF
        return {0x0A: "es", 0x04: "zh", 0x11: "ja", 0x07: "de", 0x0C: "fr"}.get(primary, "en")
    except Exception:
        return "en"

def patternsFor(language):
    """The language's translations with {} in them, as patterns to match whole messages against, most specific first"""
    if language not in _patterns:
        rows = []
        for english, translated in TRANSLATIONS.get(language, {}).items():
            if "{}" in english:
                pattern = re.compile("(.*?)".join(re.escape(part) for part in english.split("{}")), re.DOTALL)
                rows.append((len(english) - 2 * english.count("{}"), pattern, translated))
        rows.sort(key=lambda row: -row[0])
        _patterns[language] = [(pattern, translated) for _, pattern, translated in rows]
    return _patterns[language]

def T(text, depth=0):
    """The text in the chosen language: unchanged in English, or when there is no translation for it"""
    if LANGUAGE == "en" or not isinstance(text, str) or not text:
        return text
    table = TRANSLATIONS.get(LANGUAGE, {})
    if text in table:
        return table[text]
    if depth < 3 and "{" not in text:
        for pattern, translated in patternsFor(LANGUAGE):
            match = pattern.fullmatch(text)
            if match:
                return translated.format(*(T(part, depth + 1) for part in match.groups()))
    return text

# ---- files and folders ---------------------------------------------------------------------------------------
# Next to the .exe when frozen, next to this script otherwise:
#   data/         what the app saves: library, tag cache, playlists, stations, settings
#   assets/       the icon and the default background picture (the first .jpg, else .png, in there)
#   User_Music/   songs in here are always in the library
#   audio_engine/ the C# audio engine and NAudio, run by PowerShell
#   vosk_model/   the speech model, only when voice control is installed
BASE_DIR = Path(sys.executable).parent if getattr(sys, "frozen", False) else Path(__file__).resolve().parent
DATA_DIR = BASE_DIR / "data"
ASSETS_DIR = BASE_DIR / "assets"
songFolderPath = BASE_DIR / "User_Music"
LIBRARY_FILE = DATA_DIR / "library.json" # paths of the songs dropped in, they stay where they are
TAGS_FILE = DATA_DIR / "tags.json" # artist/album/track read from the song files, so they aren't re-read every launch
PLAYLISTS_FILE = DATA_DIR / "playlists.json" # your own playlists: name, song file paths, sort order
STATIONS_FILE = DATA_DIR / "stations.json" # your own stations and their order live here
SETTINGS_FILE = DATA_DIR / "settings.json" # background, theme colour, equalizer, fades, sort/loop/shuffle choices
ICON_FILE = "assets/LettucePlayer.ico"
VOSK_DIR = "vosk_model" # the small English Vosk model, next to the script/exe (or bundled in it)

def moveOldFiles():
    """Older versions kept everything loose next to the app, and the songs folder was called irrelevant_folder: moves
    them into today's folders, so nothing is lost on updating"""
    try:
        DATA_DIR.mkdir(exist_ok=True)
        for file in (LIBRARY_FILE, TAGS_FILE, PLAYLISTS_FILE, STATIONS_FILE, SETTINGS_FILE):
            old = BASE_DIR / file.name
            if old.is_file() and not file.exists():
                old.replace(file)
        old = BASE_DIR / "irrelevant_folder"
        if old.is_dir() and not songFolderPath.exists():
            old.rename(songFolderPath)
        # the profile of the first YouTube window, which opened youtube.com itself: its browser could bring those tabs back
        shutil.rmtree(DATA_DIR / "youtube_browser", ignore_errors=True)
    except OSError:
        pass # a read-only folder: the app still runs, it just can't save

SONG_SUFFIXES = {".mp3", ".m4a", ".mp4", ".wav", ".wma"}
DROP_SUFFIXES = SONG_SUFFIXES | {".xspf"}
SONG_TYPES = [("Music", "*.mp3 *.m4a *.mp4 *.wav *.wma"), ("All files", "*.*")]
PICTURE_TYPES = [("Pictures", "*.jpg *.jpeg *.png *.bmp *.gif *.webp"), ("All files", "*.*")]

# ---- choices --------------------------------------------------------------------------------------------------
LOOP_MODES = {"off": "Loop: Off", "list": "Loop: List", "one": "Loop: 1"}
COMPACT_LOOP_MODES = {"off": "Loop", "list": "Loop all", "one": "Loop 1"} # the narrow players' shorter words
SORT_MODES = [("name", "Name"), ("number", "#"), ("album", "Album"), ("artist", "Artist")]
LIST_SORT_MODES = [("", "Added")] + SORT_MODES # the library and playlists can also keep the order their songs were added in
VOICE_COMMANDS = ["time", "date", "rick", "snow", "rain", "playlist", "radio", "stop", "pause", "resume", "continue", "next", "skip",
                  "previous", "back", "mute", "unmute", "end", "exit"]
HIDDEN_SONG = "never gonna give you up" # never shown in the song list
VIS_BARS = 14 # bars in the header visualizer (audio_engine/engine.cs reports the same number of levels)
CONNECT_TIMEOUT = 8 # seconds to wait for a radio station
DEFAULT_STATIONS = [
    {"name": "Jazz", "url": "http://bobcatradio.hisd.com:8000/main"},
    {"name": "Electro", "url": "https://stream.bigfm.de/edm/mp3-128/"},
    {"name": "Trance", "url": "https://s3.slotex.pl:7252/;"},
    {"name": "Christian", "url": "https://maestro.emfcdn.com/stream_for/k-love/web/aac"},
    {"name": "Disco", "url": "https://antares.dribbcast.com/proxy/s8190/stream"},
]

# ---- colours and fonts ----------------------------------------------------------------------------------------
BG, TEXT, MUTED = "#0f1115", "#e6e8ee", "#a3a9bb"
DEFAULT_ACCENT = "#f1ee7c" # rgb(241, 238, 124)
ACCENT = DEFAULT_ACCENT # the theme colour, changed with setAccent()
THEME_COLORS = ["#f1ee7c", "#6c8cff", "#a77bff", "#ff6fae", "#ff6b6b", "#ff9a4d", "#3ecf8e", "#3cc9d6", "#ffffff", "#000000"]
STATUS_COLORS = {"info": MUTED, "ok": "#3ecf8e", "error": "#ff7b7b"} # status line text, "busy" uses the theme colour
FONT = "Segoe UI"
SYMBOL_FONT = "Segoe UI Symbol" # has the button symbols; naming it saves Tk a slow search through every font for them

# ---- saving and loading ---------------------------------------------------------------------------------------
# Every load falls back to sensible defaults when a file is missing or damaged; every save returns an error message
# (or None) so the window can show what went wrong.

def loadLibrary():
    try:
        return [str(p) for p in json.loads(LIBRARY_FILE.read_text(encoding="utf-8"))]
    except (OSError, ValueError, TypeError):
        return [] # missing or damaged file: nothing dropped in yet

def saveLibrary(paths):
    """Returns an error message, or None when saved"""
    try:
        LIBRARY_FILE.write_text(json.dumps(paths, indent=2), encoding="utf-8")
    except OSError as e:
        return f"Couldn't save your library: {e}"
    return None

# Each kind of file names its tags differently: mp3, m4a, mp4 and flac through mutagen's "easy" names, wav through
# ID3 frames, wma through Windows Media attributes
TAG_KEYS = {"artist": ("artist", "albumartist", "TPE1", "TPE2", "Author", "WM/AlbumArtist"),
            "album": ("album", "TALB", "WM/AlbumTitle"), "track": ("tracknumber", "TRCK", "WM/TrackNumber")}
TAG_WRITABLE = {".mp3", ".m4a", ".mp4", ".flac", ".wav", ".wma"} # files whose details can be edited (and renamed)

def readTags(path):
    """(artist, album, track number) from the file's tags. Blank / 0 when missing or unreadable"""
    try:
        import mutagen
        tags = (mutagen.File(path, easy=True) or {}).tags or {}
    except Exception:
        return "", "", 0
    def first(field):
        for key in TAG_KEYS[field]:
            value = tags.get(key)
            value = getattr(value, "text", value) # an ID3 frame holds its values in .text
            if value:
                return str(value[0] if isinstance(value, list) else value).strip()
        return ""
    def known(text):
        return "" if text.lower().startswith("unknown") else text # players write "Unknown artist" when there's nothing
    match = re.match(r"\d+", first("track"))
    return known(first("artist")), known(first("album")), int(match.group()) if match else 0

def writeTags(path, title, artist, album, track):
    """Writes the song's title, artist, album and track number (0: none) into the file. A blank one is removed, and
    one given as None is left as it is. A track number written as "3/12" keeps its "/12". Raises an exception when the
    file can't be written"""
    import mutagen
    suffix = Path(path).suffix.lower()
    def numbered(old):
        old = getattr(old, "text", old) # an ID3 frame holds its values in .text
        old = str(old[0]) if isinstance(old, list) and old else str(old or "")
        return None if track is None else "" if not track else f"{track}/{old.split('/', 1)[1]}" if "/" in old else str(track)
    if suffix == ".wav":
        from mutagen.id3 import TALB, TIT2, TPE1, TRCK
        from mutagen.wave import WAVE
        song = WAVE(path)
        if song.tags is None:
            song.add_tags()
        values = ((TIT2, title), (TPE1, artist), (TALB, album), (TRCK, numbered(song.tags.get("TRCK"))))
        for frame, value in values:
            if value is None:
                continue
            song.tags.delall(frame.__name__)
            if value:
                song.tags.add(frame(encoding=3, text=value))
    elif suffix == ".wma":
        from mutagen.asf import ASF
        song = ASF(path)
        values = (("Title", title), ("Author", artist), ("WM/AlbumTitle", album), ("WM/TrackNumber", numbered(song.tags.get("WM/TrackNumber"))))
        for key, value in values:
            if value is None:
                continue
            if value:
                song.tags[key] = [value]
            elif key in song.tags:
                del song.tags[key]
    else: # mp3, m4a, mp4, flac
        song = mutagen.File(path, easy=True)
        if song is None:
            raise ValueError("it isn't a music file mutagen recognises")
        if song.tags is None:
            song.add_tags()
        values = (("title", title), ("artist", artist), ("album", album), ("tracknumber", numbered(song.tags.get("tracknumber"))))
        for key, value in values:
            if value is None:
                continue
            if value:
                song.tags[key] = value
            elif key in song.tags:
                del song.tags[key]
    song.save()

def readArt(path):
    """The cover picture (as bytes) inside the song's tags, else a cover / folder picture next to the file, else None.
    A YouTube song's cover is its thumbnail, saved when it was added"""
    if isYouTube(path):
        try:
            return (YT_COVERS_DIR / f"{youTubeId(path)}.jpg").read_bytes()
        except OSError:
            return None
    try:
        import mutagen
        song = mutagen.File(path)
        tags = song.tags if song is not None else None
        if tags is not None and hasattr(tags, "getall"): # mp3
            for frame in tags.getall("APIC"):
                return frame.data
        if tags is not None and tags.get("covr"): # m4a
            return bytes(tags["covr"][0])
        if getattr(song, "pictures", None): # flac
            return song.pictures[0].data
    except Exception:
        pass
    try:
        for name in ("cover", "folder", "front", "album", "albumart"):
            for suffix in (".jpg", ".jpeg", ".png"):
                picture = Path(path).with_name(name + suffix)
                if picture.is_file():
                    return picture.read_bytes()
    except Exception:
        pass
    return None

ART_TYPES = {".mp3", ".m4a", ".mp4", ".flac", ".wav"} # files that can hold album art (a wma's pictures aren't read)
ART_SIZE = 1000 # album art is saved this many pixels a side at most: sharp on the biggest cover the app draws
ART_MIN = 500 # the smallest picture the Album art window recommends

def preparedArt(path):
    """A picture file made into album art: the middle square, shrunk to ART_SIZE a side when bigger, as JPEG bytes
    (a transparent picture goes onto black). Raises OSError / ValueError when it isn't a picture that can be read"""
    with Image.open(path) as picture:
        picture = ImageOps.exif_transpose(picture) # a phone photo the right way up
        picture = Image.alpha_composite(Image.new("RGBA", picture.size, (0, 0, 0, 255)), picture.convert("RGBA")).convert("RGB")
    side = min(picture.size)
    left, top = (picture.width - side) // 2, (picture.height - side) // 2
    picture = picture.crop((left, top, left + side, top + side))
    if side > ART_SIZE:
        picture = picture.resize((ART_SIZE, ART_SIZE), Image.LANCZOS)
    out = io.BytesIO()
    picture.save(out, "JPEG", quality=90)
    return out.getvalue()

def writeArt(path, data):
    """Writes the album art (JPEG bytes from preparedArt) into the song file, in place of any it had; None removes it.
    Raises an exception when the file can't be written"""
    import mutagen
    suffix = Path(path).suffix.lower()
    song = mutagen.File(path)
    if song is None:
        raise ValueError("it isn't a music file mutagen recognises")
    if suffix == ".flac":
        from mutagen.flac import Picture
        song.clear_pictures()
        if data:
            picture = Picture()
            picture.type, picture.mime, picture.desc, picture.data = 3, "image/jpeg", "Cover", data # 3: the front cover
            picture.width, picture.height = Image.open(io.BytesIO(data)).size
            picture.depth = 24
            song.add_picture(picture)
    else:
        if song.tags is None:
            song.add_tags()
        if suffix in (".m4a", ".mp4"):
            from mutagen.mp4 import MP4Cover
            if data:
                song.tags["covr"] = [MP4Cover(data, imageformat=MP4Cover.FORMAT_JPEG)]
            elif "covr" in song.tags:
                del song.tags["covr"]
        else: # mp3, wav: ID3
            from mutagen.id3 import APIC
            song.tags.delall("APIC")
            if data:
                song.tags.add(APIC(encoding=3, mime="image/jpeg", type=3, desc="Cover", data=data))
    song.save()

def fitText(font, text, width):
    """The text cut short with "..." so it is no wider than width (unchanged when it fits)"""
    if font.measure(text) <= width:
        return text
    while text and font.measure(text + "...") > width:
        text = text[:-1]
    return text.rstrip() + "..."

def wrappedLines(font, text, width):
    """How many lines Tk's word wrapping makes of the text at this width (a word too long for a line is split)"""
    count, line = 1, ""
    for word in text.split(" "):
        trial = f"{line} {word}" if line else word
        if font.measure(trial) <= width:
            line = trial
            continue
        if line:
            count += 1
        while len(word) > 1 and font.measure(word) > width: # a very long word runs on over several lines
            cut = len(word) - 1
            while cut > 1 and font.measure(word[:cut]) > width:
                cut -= 1
            word = word[cut:]
            count += 1
        line = word
    return count

def fitLines(font, text, width, lines):
    """The text cut short with "..." so it wraps onto no more than this many lines (unchanged when it fits)"""
    if wrappedLines(font, text, width) <= lines:
        return text
    low, high = 0, len(text) # the longest start of it that still fits, found by halving
    while low < high:
        middle = (low + high + 1) // 2
        if wrappedLines(font, text[:middle].rstrip() + "...", width) <= lines:
            low = middle
        else:
            high = middle - 1
    return text[:low].rstrip() + "..."

LRC_TIME = re.compile(r"\[(\d+):(\d+(?:[.:]\d+)?)\]") # [mm:ss.xx], the time a line is sung at

def loadLyrics(path):
    """The song's lyrics, from an .lrc file in the same folder with exactly the song's name ("Song.mp3" -> "Song.lrc").
    [(seconds, text)] in order for timed lyrics, [(None, text)] for an .lrc without times, None when there is none.
    Understands several times on one line, [offset:ms], and the word timings of "enhanced" .lrc files (dropped)"""
    if not path or "://" in str(path): # radio and YouTube songs have no folder
        return None
    try:
        raw = Path(path).with_suffix(".lrc").read_bytes()
    except OSError:
        return None
    for encoding in ("utf-8-sig", "cp1252"):
        try:
            text = raw.decode(encoding)
            break
        except UnicodeDecodeError:
            continue
    else:
        return None
    offset, timed, plain = 0.0, [], []
    for line in text.splitlines():
        shift = re.match(r"\s*\[offset:\s*([+-]?\d+)\s*\]", line, re.IGNORECASE)
        if shift:
            offset = int(shift.group(1)) / 1000 # positive: the lyrics come sooner
            continue
        times = LRC_TIME.findall(line)
        words = re.sub(r"<\d+:\d+(?:[.:]\d+)?>", "", LRC_TIME.sub("", line)).strip()
        if times:
            for minutes, seconds in times:
                timed.append((max(int(minutes) * 60 + float(seconds.replace(":", ".")) - offset, 0.0), words))
        elif line.strip() and not re.fullmatch(r"\s*\[[A-Za-z#]+:.*\]\s*", line): # not a tag like [ar:Artist]
            plain.append((None, line.strip()))
    if timed:
        return sorted(timed, key=lambda entry: entry[0])
    return plain or None

def blend(a, b, amount):
    """The colour amount of the way from a to b (each "#rrggbb" or an (r, g, b) tuple), as a "#rrggbb" string"""
    a, b = (hexToRgb(c) if isinstance(c, str) else c for c in (a, b))
    return "#%02x%02x%02x" % tuple(round(x + (y - x) * min(max(amount, 0), 1)) for x, y in zip(a, b))

def artImage(data, size, radius):
    """The cover as a rounded square of the given size (cropped to fit, not stretched)"""
    picture = Image.open(io.BytesIO(data)).convert("RGBA")
    side = min(picture.size)
    left, top = (picture.width - side) // 2, (picture.height - side) // 2
    picture = picture.crop((left, top, left + side, top + side)).resize((size, size), Image.LANCZOS)
    picture.putalpha(roundedMask(size, size, radius))
    return ImageTk.PhotoImage(picture)

def loadTagCache():
    try:
        return {k: v for k, v in json.loads(TAGS_FILE.read_text(encoding="utf-8")).items() if isinstance(v, dict)}
    except (OSError, ValueError, AttributeError):
        return {}

def saveTagCache(cache):
    try:
        TAGS_FILE.write_text(json.dumps(cache), encoding="utf-8")
    except OSError:
        pass # only a speed-up, nothing to tell the user

def loadPlaylists():
    try:
        data = json.loads(PLAYLISTS_FILE.read_text(encoding="utf-8"))
        return [{"name": str(pl["name"]), "tracks": [str(t) for t in pl.get("tracks", [])],
                 "sort": pl.get("sort") if pl.get("sort") in dict(SORT_MODES) else "", "reverse": pl.get("reverse") is True}
                for pl in data]
    except (OSError, ValueError, KeyError, TypeError, AttributeError):
        return [] # missing or damaged file: no playlists yet

def savePlaylists(playlists):
    """Returns an error message, or None when saved"""
    try:
        PLAYLISTS_FILE.write_text(json.dumps(playlists, indent=2), encoding="utf-8")
    except OSError as e:
        return f"Couldn't save your playlists: {e}"
    return None

def loadStations():
    try:
        data = json.loads(STATIONS_FILE.read_text(encoding="utf-8"))
        stations = [{"name": str(st["name"]), "url": str(st["url"])} for st in data]
        if stations:
            return stations
    except (OSError, ValueError, KeyError, TypeError):
        pass # missing or damaged file: start from the defaults
    return [dict(st) for st in DEFAULT_STATIONS]

def saveStations(stations):
    """Returns an error message, or None when saved"""
    try:
        STATIONS_FILE.write_text(json.dumps(stations, indent=2), encoding="utf-8")
    except OSError as e:
        return f"Couldn't save your stations: {e}"
    return None

def loadSettings():
    settings = {"background": "", "nightMode": False, "nightBackground": "", "fun": True, "youtube": True, "cover": False, "pictureTitleBar": True, "language": "", "accent": DEFAULT_ACCENT, "sort": "name", "reverse": False, "loop": "off",
                "shuffle": False, "fadeIn": 1.5, "fadeOut": 1.5, "eq": {"bass": 0.0, "mid": 0.0, "treble": 0.0}}
    try:
        saved = json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
        settings["background"] = str(saved.get("background", ""))
        settings["nightMode"] = saved.get("nightMode") is True
        settings["fun"] = saved.get("fun") is not False # on unless it was switched off
        settings["youtube"] = saved.get("youtube") is not False
        settings["cover"] = saved.get("cover") is True # the playing song's cover as the background
        if saved.get("language") in LANGUAGES:
            settings["language"] = saved["language"]
        settings["pictureTitleBar"] = saved.get("pictureTitleBar") is not False # on unless switched off: the title bar in the picture's colour, not the theme's
        settings["nightBackground"] = str(saved.get("nightBackground", ""))
        if saved.get("sort") in dict(LIST_SORT_MODES):
            settings["sort"] = saved["sort"]
        settings["reverse"] = saved.get("reverse") is True
        settings["shuffle"] = saved.get("shuffle") is True
        for key in ("fadeIn", "fadeOut"):
            settings[key] = max(0.0, min(10.0, float(saved.get(key, 1.5))))
        if saved.get("loop") in LOOP_MODES:
            settings["loop"] = saved["loop"]
        accent = str(saved.get("accent", ""))
        if len(accent) == 7 and accent[0] == "#" and all(c in "0123456789abcdefABCDEF" for c in accent[1:]):
            settings["accent"] = accent.lower()
        for band in settings["eq"]:
            settings["eq"][band] = max(-12.0, min(12.0, float(saved.get("eq", {}).get(band, 0))))
    except (OSError, ValueError, AttributeError, TypeError):
        pass # missing or damaged file: defaults
    return settings

def saveSettings(settings):
    """Returns an error message, or None when saved"""
    try:
        SETTINGS_FILE.write_text(json.dumps(settings, indent=2), encoding="utf-8")
    except OSError as e:
        return f"Couldn't save your settings: {e}"
    return None

# ---- radio ----------------------------------------------------------------------------------------------------
def checkStream(url):
    """Connects to a station and returns a plain-language reason it can't play, or None when it looks fine"""
    host = urlparse(url).hostname or url
    try:
        request = urllib.request.Request(url, headers={"Icy-MetaData": "1", "User-Agent": "Mozilla/5.0"})
        with urllib.request.urlopen(request, timeout=CONNECT_TIMEOUT) as response:
            kind = response.headers.get_content_type()
    except urllib.error.HTTPError as e:
        if e.code in (401, 403):
            return f"The station refused access (HTTP {e.code}). It may need a login or block outside apps."
        if e.code in (404, 410):
            return f"Stream not found (HTTP {e.code}). The address may be wrong or the station moved."
        if e.code >= 500:
            return f"The station's server has a problem (HTTP {e.code}). It's probably offline for now, try again later."
        return f"The station answered with an error (HTTP {e.code})."
    except HTTPException:
        return None # Shoutcast-style replies that aren't strict HTTP still play fine
    except (urllib.error.URLError, OSError) as e:
        reason = getattr(e, "reason", e)
        if isinstance(reason, socket.gaierror):
            return f"Can't find the server '{host}'. Check the web address, or your internet connection."
        if isinstance(reason, (TimeoutError, socket.timeout)):
            return f"No answer from '{host}' within {CONNECT_TIMEOUT} seconds. The station may be offline or your internet is slow."
        if isinstance(reason, ConnectionRefusedError):
            return f"'{host}' refused the connection. The station may be down, or the port in the address is wrong."
        if isinstance(reason, ssl.SSLError):
            return f"The secure (https) connection to '{host}' failed: {reason}. Try the http:// version of the address."
        return f"Couldn't connect to '{host}': {reason}"
    lowered = url.lower().split("?")[0]
    if kind == "text/html":
        return "That address is a web page, not an audio stream. Look for the station's direct stream URL."
    if kind in ("audio/x-mpegurl", "audio/mpegurl", "application/vnd.apple.mpegurl", "audio/x-scpls", "application/pls+xml") \
            or lowered.endswith((".m3u", ".m3u8", ".pls")):
        return "That address is a playlist file (.m3u / .pls), not the stream itself. Open it in a text editor and use the stream URL inside."
    return None

# ---- YouTube --------------------------------------------------------------------------------------------------
# A YouTube song is stored as its watch address. YouTube only lets its own player play its videos, so these songs
# don't go through the audio engine: they play in YouTube's official embedded player (the IFrame Player API), on a
# small page the app serves itself from 127.0.0.1 and opens as an app window of a browser with a profile of its own
# (the default browser when it is Chrome, Edge, Brave or Vivaldi, else Chrome, else Edge, which every Windows 11 PC
# has). The page reports what the player is doing twice a second and picks up the app's commands in the answer, so the
# next YouTube song loads in the same window, the app knows when a video ends, and the window closes once the queue
# moves on to a file, ends or is stopped. (Driving youtube.com itself over the browser's DevTools protocol doesn't
# work: YouTube takes a remotely controlled browser for a bot and stops many videos about 50 seconds in.)
YT_TAG = "[YOUTUBE] " # in front of a YouTube song's name in the lists
YT_WATCH = "https://www.youtube.com/watch?v="
YT_ID = re.compile(r"(?:youtube\.com/(?:watch\?(?:[^#]*&)?v=|shorts/|embed/|live/)|youtu\.be/)([A-Za-z0-9_-]{11})")
YT_COVERS_DIR = DATA_DIR / "youtube_covers" # each video's thumbnail, fetched when it is added
YT_PROFILE_DIR = DATA_DIR / "youtube_player" # the browser profile the YouTube window uses
CHROMIUM_BROWSERS = {"chrome.exe", "msedge.exe", "brave.exe", "vivaldi.exe", "chromium.exe"} # browsers with app windows

def youTubeId(text):
    """The 11-character video id in a YouTube link (watch, youtu.be, shorts, embed or live), or None"""
    match = YT_ID.search(str(text))
    return match.group(1) if match else None

def isYouTube(path):
    return str(path).startswith(YT_WATCH)

def plainName(name):
    """A song's name without the [YOUTUBE] tag, for sorting and for the voice commands"""
    return name[len(YT_TAG):] if name.startswith(YT_TAG) else name

def fetchYouTubeInfo(videoId):
    """(title, channel) from YouTube's oEmbed address, which needs no API key, and saves the video's thumbnail as its
    cover. Raises ValueError with a plain-language reason when the video can't be added"""
    url = YT_WATCH + videoId
    try:
        request = urllib.request.Request("https://www.youtube.com/oembed?format=json&url=" + quote(url, safe=""),
                                         headers={"User-Agent": "Mozilla/5.0"})
        with urllib.request.urlopen(request, timeout=CONNECT_TIMEOUT) as response:
            info = json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        if e.code in (400, 404):
            raise ValueError("YouTube has no video at that address. It may be private or deleted.")
        if e.code in (401, 403):
            raise ValueError("Its owner doesn't let it play outside youtube.com, so Lettuce Player can't play it.")
        else:
            raise ValueError(f"YouTube answered with an error (HTTP {e.code}). Try again later.")
    except (urllib.error.URLError, OSError, ValueError) as e:
        raise ValueError(f"Couldn't reach YouTube: {getattr(e, 'reason', e)}. Check your internet connection.")
    saveYouTubeCover(videoId)
    return str(info.get("title") or f"YouTube video {videoId}"), str(info.get("author_name") or "")

# A video's thumbnails, best first. The full-size one (1280 x 720) only exists for HD uploads; the others are 4:3 with the
# video letterboxed inside them
YT_THUMBNAILS = ("maxresdefault", "sddefault", "hqdefault")

def saveYouTubeCover(videoId):
    """Saves the best thumbnail YouTube has for the video as its cover, with any black bars cut off. False when there
    was none to get (the song still plays, without a cover)"""
    for name in YT_THUMBNAILS:
        try:
            with urllib.request.urlopen(f"https://i.ytimg.com/vi/{videoId}/{name}.jpg", timeout=CONNECT_TIMEOUT) as response:
                data = response.read()
            picture = Image.open(io.BytesIO(data))
            picture.load()
        except (urllib.error.URLError, OSError, ValueError):
            continue # not made for this video: the next size down
        if picture.width < 200:
            continue # YouTube's grey "no thumbnail" placeholder
        trimmed = trimBars(picture.convert("RGB"))
        if trimmed.size != picture.size: # bars cut off: saved again, at high quality
            out = io.BytesIO()
            trimmed.save(out, "JPEG", quality=92)
            data = out.getvalue()
        try:
            YT_COVERS_DIR.mkdir(parents=True, exist_ok=True)
            (YT_COVERS_DIR / f"{videoId}.jpg").write_bytes(data)
        except OSError:
            return False
        return True
    return False

def trimBars(picture):
    """The picture without the black bars around a letterboxed (or pillarboxed) video. Only even bars on opposite
    sides are cut, so a dark scene at one edge stays whole"""
    box = picture.convert("L").point(lambda v: 255 if v > 28 else 0).getbbox()
    if not box:
        return picture # all black
    left, top, right, bottom = box
    w, h = picture.size
    if abs(top - (h - bottom)) > 4 or top < h * 0.03: # bars above and below are the same height
        top, bottom = 0, h
    if abs(left - (w - right)) > 4 or left < w * 0.03:
        left, right = 0, w
    return picture.crop((left, top, right, bottom)) if (left, top, right, bottom) != (0, 0, w, h) else picture

def upgradeYouTubeCovers(videoIds):
    """Background thread: covers saved by older versions are the small letterboxed thumbnail (480 x 360). Each one is
    swapped for the best one YouTube has. Returns how many were improved"""
    better = 0
    for videoId in videoIds:
        try:
            with Image.open(YT_COVERS_DIR / f"{videoId}.jpg") as picture:
                if picture.size != (480, 360):
                    continue # already the best one
        except OSError:
            pass # none yet: fetch one
        better += saveYouTubeCover(videoId)
    return better

def findChromium():
    """The browser YouTube songs play in: the default browser when it can open app windows, else Chrome, else Edge.
    None when none of them is installed"""
    import winreg
    candidates = []
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                            r"Software\Microsoft\Windows\Shell\Associations\UrlAssociations\https\UserChoice") as key:
            progId = winreg.QueryValueEx(key, "ProgId")[0]
        with winreg.OpenKey(winreg.HKEY_CLASSES_ROOT, progId + r"\shell\open\command") as key:
            command = winreg.QueryValueEx(key, "")[0]
        match = re.match(r'\s*"([^"]+)"|\s*(\S+)', command)
        candidates.append(match.group(1) or match.group(2))
    except (OSError, AttributeError):
        pass # no default set: try Chrome and Edge
    roots = [os.environ.get(name) for name in ("PROGRAMFILES", "PROGRAMFILES(X86)", "LOCALAPPDATA")]
    for exe in (r"Google\Chrome\Application\chrome.exe", r"Microsoft\Edge\Application\msedge.exe"):
        candidates += [os.path.join(root, exe) for root in roots if root]
    for exe in candidates:
        if os.path.basename(exe).lower() in CHROMIUM_BROWSERS and os.path.isfile(exe):
            return exe
    return None

class YouTubeClosed(Exception):
    """The YouTube window was closed (by hand, or the browser quit)"""

# The page in the YouTube window. It plays YouTube's embedded player, sends the player's state to /sync twice a second
# and runs the commands that come back: "load <id>", "close", or one of the player's own functions like "seekTo(30, true)".
# If the app stops answering (it was closed or crashed), the window closes itself.
YT_WINDOW_TITLE = "Lettuce Player - YouTube" # the page's title, which is also its window's: how the window is found
YT_PLAYER_PAGE = """<!doctype html>
<html><head><meta charset="utf-8"><title>Lettuce Player - YouTube</title>
<style>html, body { margin: 0; height: 100%; background: #0f1115; overflow: hidden } #player { width: 100%; height: 100% }</style>
</head><body><div id="player"></div>
<script>
const token = "%TOKEN%", allowed = ["playVideo", "pauseVideo", "seekTo", "setVolume", "mute", "unMute"];
let player = null, want = "%VIDEO%", error = 0, failures = 0;
const api = document.createElement("script");
api.src = "https://www.youtube.com/iframe_api";
document.head.appendChild(api);
function onYouTubeIframeAPIReady() {
    player = new YT.Player("player", {videoId: want, width: "100%", height: "100%",
        playerVars: {autoplay: 1, playsinline: 1, rel: 0},
        events: {onReady: () => player.playVideo(), onError: event => { error = event.data; }}});
}
function run(command) {
    if (command === "close") { window.close(); return; }
    if (command.startsWith("load ")) { want = command.slice(5); error = 0; if (player) player.loadVideoById(want); return; }
    const call = /^(\\w+)\\((.*)\\)$/.exec(command);
    if (call && allowed.includes(call[1]) && player && player[call[1]]) player[call[1]](...JSON.parse("[" + call[2] + "]"));
}
async function sync() {
    const ready = player && player.getPlayerState;
    const state = ready ? {id: (player.getVideoData() || {}).video_id || "", want, error, state: player.getPlayerState(),
                           time: player.getCurrentTime() || 0, duration: player.getDuration() || 0}
                        : {id: "", want, error, state: null};
    try {
        const answer = await fetch("/sync?token=" + token, {method: "POST", body: JSON.stringify(state)});
        (await answer.json()).commands.forEach(run);
        failures = 0;
    } catch (e) {
        if (++failures > 10) window.close(); // the app is gone
    }
    setTimeout(sync, 500);
}
sync();
addEventListener("pagehide", () => navigator.sendBeacon("/sync?token=" + token + "&closed=1"));
</script></body></html>"""

YT_ERRORS = {2: "YouTube says the video address is wrong.", 5: "The browser can't play this video.",
             100: "The video was removed or made private.", 101: "Its owner doesn't let it play outside youtube.com.",
             150: "Its owner doesn't let it play outside youtube.com.", 153: "YouTube refused the player page."}

class YouTubeBrowser:
    """The window YouTube songs play in: the player page above, served from 127.0.0.1 (with a secret in its address,
    so no other page can talk to it) and opened as an app window of the browser. The playback thread calls open(),
    state() and control(); the page's requests arrive on the server's threads; a lock keeps them apart"""

    def __init__(self, profile=YT_PROFILE_DIR, title=YT_WINDOW_TITLE):
        """profile: the browser profile it uses, title: its window's title. Channel two has its own of both, so its window
        runs beside channel one's and is told apart from it"""
        self.profile, self.title = profile, title
        self.lock = threading.Lock()
        self.server = self.proc = None
        self.token = secrets.token_urlsafe(16)
        self.commands = [] # waiting for the page's next visit
        self.latest = None # the player's state as the page last reported it
        self.launched = 0.0 # when the window was opened, 0 while there is none
        self.lastSync = 0.0 # when the page last reported in

    def isOpen(self):
        return self.launched > 0

    def serve(self):
        """Starts the little web server the page talks to, on a free port"""
        from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
        browser = self

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, *args):
                pass # nothing to print to

            def reply(self, code, kind, body):
                self.send_response(code)
                self.send_header("Content-Type", kind)
                self.send_header("Cache-Control", "no-store")
                self.end_headers()
                self.wfile.write(body)

            def do_GET(self):
                url = urlparse(self.path)
                query = parse_qs(url.query)
                video = query.get("v", [""])[0]
                if url.path == "/player" and query.get("token") == [browser.token] and re.fullmatch(r"[A-Za-z0-9_-]{11}", video):
                    page = YT_PLAYER_PAGE.replace("%TOKEN%", browser.token).replace("%VIDEO%", video)
                    page = page.replace(f"<title>{YT_WINDOW_TITLE}</title>", f"<title>{browser.title}</title>")
                    self.reply(200, "text/html; charset=utf-8", page.encode("utf-8"))
                else:
                    self.reply(404, "text/plain", b"")

            def do_POST(self):
                url = urlparse(self.path)
                query = parse_qs(url.query)
                if url.path != "/sync" or query.get("token") != [browser.token]:
                    self.reply(403, "text/plain", b"")
                    return
                body = self.rfile.read(int(self.headers.get("Content-Length") or 0))
                with browser.lock:
                    if query.get("closed"): # the window is closing
                        browser.launched, browser.latest = 0.0, None
                        commands = []
                    else:
                        try:
                            browser.latest = json.loads(body or b"null")
                        except ValueError:
                            pass
                        browser.lastSync = time.time()
                        browser.launched = browser.launched or browser.lastSync # reloaded by hand: it's back
                        commands, browser.commands = browser.commands, []
                self.reply(200, "application/json", json.dumps({"commands": commands}).encode("utf-8"))

        self.server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.server.handle_error = lambda request, address: None # a window closing mid-answer drops the connection: fine
        threading.Thread(target=self.server.serve_forever, daemon=True).start()

    def alive(self):
        """The window is open and answering (or still starting up)"""
        return self.launched > 0 and time.time() - max(self.lastSync, self.launched) < (25 if not self.lastSync else 6)

    def open(self, url):
        """Shows the video: in the window that's already open, or in a new one"""
        videoId = youTubeId(url)
        with self.lock:
            if self.alive():
                self.commands.append("load " + videoId)
                self.latest = None
                return
        self.launch(videoId)

    def launch(self, videoId):
        exe = findChromium()
        if not exe:
            raise RuntimeError("YouTube songs need Google Chrome or Microsoft Edge. Install one, or turn YouTube off in Settings.")
        if not self.server:
            self.serve()
        with self.lock:
            self.commands, self.latest, self.lastSync, self.launched = [], None, 0.0, time.time()
        # "localhost", not 127.0.0.1: some videos refuse to play on a page whose address is a bare IP address
        page = f"http://localhost:{self.server.server_port}/player?token={self.token}&v={videoId}"
        self.profile.mkdir(parents=True, exist_ok=True)
        self.proc = subprocess.Popen(
            [exe, f"--user-data-dir={self.profile}", "--no-first-run", "--no-default-browser-check",
             "--autoplay-policy=no-user-gesture-required", "--hide-crash-restore-bubble",
             # it keeps reporting in while it's hidden behind other windows or minimised
             "--disable-background-timer-throttling", "--disable-renderer-backgrounding", "--disable-backgrounding-occluded-windows",
             "--window-size=720,450", f"--app={page}"],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    def state(self):
        """What YouTube's player is doing: {id, want, state, time, duration, error, ad}, None while the page loads. The
        state is YouTube's: -1 unstarted, 0 ended, 1 playing, 2 paused, 3 buffering, 5 cued. Raises YouTubeClosed when
        the window is gone"""
        with self.lock:
            if not self.alive():
                self.launched = 0.0
                raise YouTubeClosed()
            latest = self.latest
        if not latest or latest.get("state") is None:
            return None
        return {"id": latest.get("id", ""), "want": latest.get("want", ""), "state": latest["state"], "ad": False,
                "time": latest.get("time", 0), "duration": latest.get("duration", 0), "error": latest.get("error", 0)}

    def minimize(self):
        """Minimizes the window (found by its page's title), so only the music is noticed. False while it isn't there yet"""
        import ctypes
        from ctypes import wintypes as wt
        user32 = ctypes.WinDLL("user32") # its own copy, so the types set here don't leak out
        found = []
        title = ctypes.create_unicode_buffer(64)

        @ctypes.WINFUNCTYPE(wt.BOOL, wt.HWND, wt.LPARAM)
        def check(hwnd, _):
            user32.GetWindowTextW(hwnd, title, 64)
            if title.value in (self.title, self.title + " - YouTube") and user32.IsWindowVisible(hwnd):
                found.append(hwnd)
            return True
        user32.EnumWindows(check, 0)
        for hwnd in found:
            if not user32.IsIconic(hwnd):
                # in front (just opened): minimizing hands the focus back; behind: it's minimized without taking it
                user32.ShowWindow(hwnd, 6 if user32.GetForegroundWindow() == hwnd else 7) # SW_MINIMIZE, SW_SHOWMINNOACTIVE
        return bool(found)

    def control(self, call):
        """Calls one of YouTube's player functions, like "pauseVideo()" or "seekTo(30, true)\""""
        with self.lock:
            if self.launched:
                self.commands.append(call)

    def close(self):
        """Asks the page to close its window, and closes the browser if it doesn't within two seconds"""
        with self.lock:
            if not self.launched:
                return
            self.commands.append("close")
        end = time.time() + 2
        while self.launched and time.time() < end:
            time.sleep(0.1)
        with self.lock:
            stillOpen, self.launched = self.launched, 0.0
        if stillOpen and self.proc and self.proc.poll() is None:
            subprocess.run(["taskkill", "/F", "/T", "/PID", str(self.proc.pid)], creationflags=subprocess.CREATE_NO_WINDOW,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

# Audio runs in ONE long-lived hidden PowerShell process, so tracks don't each pay PowerShell's start-up cost. It loads
# the NAudio DLLs and audio_engine/engine.cs (decode through Windows Media Foundation, 3-band EQ, volume and fades).
# Commands arrive on stdin: "play <id> <uri>", "stop", "pause", "resume", "vol <0-1>", "mute <0|1>", "seek <seconds>",
# "eq <bassDb> <midDb> <trebleDb>", "fade <inSeconds> <outSeconds>", "listen <0|1>" (the visualizer hears the speakers, for YouTube songs), "quit". It answers on stdout with "pos <id> <seconds> <duration>" while a track plays
# (duration is 0 for live streams), "vis <fourteen levels 0-1>" about ten times a second, "ended <id>" when a track finishes by itself and "failed <id> <reason>".
HOST_SCRIPT = """
$ErrorActionPreference = 'Stop'
$dir = $env:LETTUCE_ENGINE
$inv = [Globalization.CultureInfo]::InvariantCulture
$out = [Console]::OpenStandardOutput() # raw stream: Console.Out stays buffered when piped
function Say($text) { $bytes = [Text.Encoding]::ASCII.GetBytes($text + [char]10); $out.Write($bytes, 0, $bytes.Length); $out.Flush() }
$dlls = 'NAudio.Core', 'NAudio.WinMM', 'NAudio.Wasapi', 'NAudio' | ForEach-Object { Join-Path $dir ($_ + '.dll') }
$dlls | ForEach-Object { Add-Type -Path $_ }
$netstandard = Join-Path ([Runtime.InteropServices.RuntimeEnvironment]::GetRuntimeDirectory()) 'netstandard.dll'
Add-Type -ReferencedAssemblies ($dlls + $netstandard + 'System.Core.dll') -TypeDefinition (Get-Content -Raw (Join-Path $dir 'engine.cs'))
[Lettuce.Rd]::Start()
$engine = New-Object Lettuce.Engine
$smtc = $false # registered in Windows' media controls, where earbud presses arrive
if ($env:LETTUCE_SMTC -ne '0') { try { Add-Type -Path (Join-Path $dir 'smtc.dll'); [Lettuce.Smtc]::Start(); $smtc = $true } catch { } }
$button = $null
$report = [Diagnostics.Stopwatch]::StartNew()
$cmd = $null
while ($true) {
    Start-Sleep -Milliseconds 10 # short, so a stop or a new song is acted on straight away
    while ([Lettuce.Rd]::Q.TryDequeue([ref]$cmd)) {
        $parts = $cmd.Split(' ', 3)
        try {
            if ($parts[0] -eq 'quit') { $engine.Stop(); exit }
            elseif ($parts[0] -eq 'play') { $engine.Play($parts[1], $parts[2]) }
            elseif ($parts[0] -eq 'stop') { $engine.StopSmooth() }
            elseif ($parts[0] -eq 'warm') { $engine.Warm() }
            elseif ($parts[0] -eq 'pause') { $engine.Pause() }
            elseif ($parts[0] -eq 'resume') { $engine.Resume() }
            elseif ($parts[0] -eq 'vol') { $engine.SetVolume([double]::Parse($parts[1], $inv)) }
            elseif ($parts[0] -eq 'mute') { $engine.SetMuted($parts[1] -eq '1') }
            elseif ($parts[0] -eq 'seek') { $engine.Seek([double]::Parse($parts[1], $inv)) }
            elseif ($parts[0] -eq 'listen') { $engine.Listen($parts[1] -eq '1') }
            elseif ($parts[0] -eq 'media') { # what Windows' media controls show: playing / paused / stopped, and the title (base64 UTF-8)
                if ($smtc) { [Lettuce.Smtc]::Show($parts[1], [Text.Encoding]::UTF8.GetString([Convert]::FromBase64String($parts[2]))) }
            }
            elseif ($parts[0] -eq 'fade') {
                $secs = $cmd.Split(' ')
                $engine.SetFades([double]::Parse($secs[1], $inv), [double]::Parse($secs[2], $inv))
            }
            elseif ($parts[0] -eq 'eq') {
                $gains = $cmd.Split(' ')
                $engine.SetEq([double]::Parse($gains[1], $inv), [double]::Parse($gains[2], $inv), [double]::Parse($gains[3], $inv))
            }
        }
        catch {
            $problem = $_.Exception
            if ($problem.InnerException) { $problem = $problem.InnerException }
            $reason = ($problem.Message -replace '[^\x20-\x7e]', ' ')
            if ($parts[0] -eq 'play') { $engine.Stop(); Say ('failed ' + $parts[1] + ' ' + $reason) }
        }
    }
    if ($smtc) { while ([Lettuce.Smtc]::Pressed.TryDequeue([ref]$button)) { Say ('button ' + $button) } }
    $engine.CheckDevice() # the song follows Windows to other speakers or headphones
    if ($engine.EndedFlag) { Say ('ended ' + $engine.CurrentId); $engine.Stop() }
    if ($engine.Active -or $engine.Listening) { Say ('vis ' + $engine.LevelsText()) }
    if ($engine.Active -and $report.ElapsedMilliseconds -ge 400) {
        $report.Restart()
        Say ('pos ' + $engine.CurrentId + ' ' + $engine.Position.ToString('0.0', $inv) + ' ' + $engine.Duration.ToString('0.0', $inv))
    }
}
"""

# ---- media keys --------------------------------------------------------------------------------------------------
MEDIA_KEYS = {0xB3: "playpause", 0xB0: "next", 0xB1: "prev", 0xB2: "stop"} # what earbud taps and keyboard media keys send

def listenForMediaKeys(events):
    """Claims the media keys system-wide, so earbuds (AirPods, Raycon...) can pause, skip and go back even when the window
    isn't focused. Runs forever in its own thread because hotkeys are delivered to the thread that registered them."""
    import ctypes
    from ctypes import wintypes
    user32 = ctypes.windll.user32
    ids = {}
    for number, key in enumerate(MEDIA_KEYS, 1):
        if user32.RegisterHotKey(None, number, 0x4000, key): # 0x4000: don't repeat while held
            ids[number] = MEDIA_KEYS[key]
    try:
        window = SeparatePlayPause(events, handleAll=not ids) # keeps its window procedure alive while the loop runs
    except Exception:
        window = None # only the keys above, then
    if not ids and not window:
        events.put(("log", "Couldn't take over the media keys (another app has them), so earbud taps won't control the player."))
        return
    message = wintypes.MSG()
    while user32.GetMessageW(ctypes.byref(message), None, 0, 0) > 0:
        if message.message == 0x0312 and message.wParam in ids: # WM_HOTKEY
            events.put(("media", ids[message.wParam], "key"))
        else:
            user32.TranslateMessage(ctypes.byref(message))
            user32.DispatchMessageW(ctypes.byref(message)) # to the hidden window below

class SeparatePlayPause:
    """AirPods (and other Bluetooth earbuds) send "play" and "pause" as two separate commands, not the play/pause toggle.
    Windows has no key for those, so the hotkeys above never see them: they arrive as input from the earbuds' media
    control device, and as an "app command" Windows passes on to the shell. A hidden window listens for both. Both
    can report the same tap, which does no harm: play only ever resumes and pause only ever pauses"""
    HID_USAGES = {0xB0: "play", 0xB1: "pause", 0xCD: "playpause", 0xB5: "next", 0xB6: "prev", 0xB7: "stop"}
    APP_COMMANDS = {46: "play", 47: "pause"} # APPCOMMAND_MEDIA_PLAY, APPCOMMAND_MEDIA_PAUSE
    WM_INPUT, HSHELL_APPCOMMAND = 0x00FF, 12

    def __init__(self, events, handleAll=False):
        """handleAll: the hotkeys couldn't be claimed, so the toggle, next, previous and stop come this way too"""
        import ctypes
        from ctypes import wintypes as wt
        self.ctypes, self.events, self.preparsed = ctypes, events, {}
        self.wanted = set(self.HID_USAGES) if handleAll else {0xB0, 0xB1} # the rest already come as hotkeys
        user32, self.hid = ctypes.WinDLL("user32"), ctypes.WinDLL("hid") # own copies, so the types set here stay here
        self.user32 = user32
        handle = ctypes.c_void_p
        for function, result, args in (
                (user32.DefWindowProcW, ctypes.c_ssize_t, [handle, wt.UINT, wt.WPARAM, wt.LPARAM]),
                (user32.CreateWindowExW, handle, [wt.DWORD, wt.LPCWSTR, wt.LPCWSTR, wt.DWORD, ctypes.c_int, ctypes.c_int,
                                                  ctypes.c_int, ctypes.c_int, handle, handle, handle, handle]),
                (user32.GetRawInputData, wt.UINT, [handle, wt.UINT, handle, ctypes.POINTER(wt.UINT), wt.UINT]),
                (user32.GetRawInputDeviceInfoW, wt.UINT, [handle, wt.UINT, handle, ctypes.POINTER(wt.UINT)]),
                (user32.RegisterShellHookWindow, wt.BOOL, [handle]),
                (self.hid.HidP_GetUsages, ctypes.c_long, [ctypes.c_int, wt.USHORT, wt.USHORT, handle,
                                                           ctypes.POINTER(wt.ULONG), handle, handle, wt.ULONG])):
            function.restype, function.argtypes = result, args

        WNDPROC = ctypes.WINFUNCTYPE(ctypes.c_ssize_t, handle, wt.UINT, wt.WPARAM, wt.LPARAM)

        class WNDCLASS(ctypes.Structure):
            _fields_ = [("style", wt.UINT), ("proc", WNDPROC), ("clsExtra", ctypes.c_int), ("wndExtra", ctypes.c_int),
                        ("instance", handle), ("icon", handle), ("cursor", handle), ("background", handle),
                        ("menu", wt.LPCWSTR), ("name", wt.LPCWSTR)]
        self.proc = WNDPROC(self.onMessage)
        kernel32 = ctypes.WinDLL("kernel32")
        kernel32.GetModuleHandleW.restype = handle
        instance = kernel32.GetModuleHandleW(None)
        self.windowClass = WNDCLASS(proc=self.proc, instance=instance, name="LettuceMediaListener")
        user32.RegisterClassW(ctypes.byref(self.windowClass))
        # a top-level window that is never shown: the shell only reports app commands to top-level windows
        self.hwnd = user32.CreateWindowExW(0x80, "LettuceMediaListener", "", 0, 0, 0, 0, 0, None, None, instance, None)
        if not self.hwnd:
            raise OSError("couldn't make the listening window")
        self.shellMessage = user32.RegisterWindowMessageW("SHELLHOOK")
        user32.RegisterShellHookWindow(self.hwnd)

        class RAWINPUTDEVICE(ctypes.Structure):
            _fields_ = [("usagePage", wt.USHORT), ("usage", wt.USHORT), ("flags", wt.DWORD), ("target", handle)]
        device = RAWINPUTDEVICE(0x0C, 0x01, 0x100, self.hwnd) # consumer controls; RIDEV_INPUTSINK: even in the background
        user32.RegisterRawInputDevices(ctypes.byref(device), 1, ctypes.sizeof(device))

    def onMessage(self, hwnd, message, wparam, lparam):
        try:
            if message == self.WM_INPUT:
                for key in self.readUsages(lparam):
                    self.events.put(("media", key, "earbuds"))
            elif message == self.shellMessage and wparam == self.HSHELL_APPCOMMAND:
                key = self.APP_COMMANDS.get(((lparam or 0) >> 16) & 0x0FFF)
                if key:
                    self.events.put(("media", key, "app command"))
        except Exception:
            pass # never let a slip here stop the messages
        return self.user32.DefWindowProcW(hwnd, message, wparam, lparam)

    def readUsages(self, lparam):
        """The media buttons pressed in one report from a media control device (none when they are let go)"""
        ctypes, user32 = self.ctypes, self.user32
        from ctypes import wintypes as wt
        headerSize = 8 + 2 * ctypes.sizeof(ctypes.c_void_p) # RAWINPUTHEADER: type, size, device, wParam
        size = wt.UINT(0)
        user32.GetRawInputData(lparam, 0x10000003, None, ctypes.byref(size), headerSize) # RID_INPUT
        data = ctypes.create_string_buffer(size.value)
        if user32.GetRawInputData(lparam, 0x10000003, data, ctypes.byref(size), headerSize) != size.value:
            return []
        raw = data.raw
        if int.from_bytes(raw[0:4], "little") != 2: # RIM_TYPEHID
            return []
        device = int.from_bytes(raw[8:8 + ctypes.sizeof(ctypes.c_void_p)], "little")
        preparsed = self.preparsedData(device)
        if preparsed is None:
            return []
        reportSize, count = int.from_bytes(raw[headerSize:headerSize + 4], "little"), int.from_bytes(raw[headerSize + 4:headerSize + 8], "little")
        found = []
        for i in range(count):
            report = ctypes.create_string_buffer(raw[headerSize + 8 + i * reportSize:headerSize + 8 + (i + 1) * reportSize], reportSize)
            usages, length = (wt.USHORT * 16)(), wt.ULONG(16)
            if self.hid.HidP_GetUsages(0, 0x0C, 0, usages, ctypes.byref(length), preparsed, report, reportSize) == 0x110000: # HIDP_STATUS_SUCCESS
                found += [self.HID_USAGES[u] for u in usages[:length.value] if u in self.wanted]
        return found

    def preparsedData(self, device):
        """What Windows knows about the device's reports, needed to read them (kept per device)"""
        if device not in self.preparsed:
            ctypes = self.ctypes
            size = ctypes.c_uint(0)
            self.user32.GetRawInputDeviceInfoW(device, 0x20000005, None, ctypes.byref(size)) # RIDI_PREPARSEDDATA
            buffer = ctypes.create_string_buffer(max(size.value, 1))
            ok = size.value and self.user32.GetRawInputDeviceInfoW(device, 0x20000005, buffer, ctypes.byref(size)) == size.value
            self.preparsed[device] = buffer if ok else None
        return self.preparsed[device]

# ---- taskbar preview buttons -------------------------------------------------------------------------------------
class ThumbBar:
    """Previous / play-pause / next buttons in the little preview that pops up when you hover over the app's taskbar
    icon. Windows only offers these through its ITaskbarList3 COM interface, reached here with ctypes, and reports
    clicks as WM_COMMAND messages to the window, so the window's message handler is wrapped to catch them. That
    handler runs in the middle of Tk's own event handling, where calling Tk crashes Python, so it only puts the click on
    the events queue and pump() acts on it"""
    PREV, PLAY, NEXT = 1, 2, 3
    WM_COMMAND, THBN_CLICKED = 0x0111, 0x1800

    def __init__(self, root, events, commands):
        """events: the app's queue for pump(). commands: {PREV: callable, PLAY: callable, NEXT: callable}"""
        import ctypes
        from ctypes import wintypes as wt
        self.ctypes, self.wt, self.events, self.commands = ctypes, wt, events, commands
        self.user32 = user32 = ctypes.windll.user32
        self.hwnd = user32.GetParent(root.winfo_id()) or root.winfo_id() # the frame window that owns the taskbar button
        self.playing, self.added = False, False

        class GUID(ctypes.Structure):
            _fields_ = [("a", ctypes.c_ulong), ("b", ctypes.c_ushort), ("c", ctypes.c_ushort), ("d", ctypes.c_ubyte * 8)]

        class THUMBBUTTON(ctypes.Structure):
            _fields_ = [("dwMask", wt.DWORD), ("iId", wt.UINT), ("iBitmap", wt.UINT), ("hIcon", wt.HICON),
                        ("szTip", ctypes.c_wchar * 260), ("dwFlags", wt.DWORD)]
        self.THUMBBUTTON = THUMBBUTTON

        ole32 = ctypes.windll.ole32
        ole32.CoInitialize(None)
        clsid, iid = GUID(), GUID()
        ole32.CLSIDFromString("{56FDF344-FD6D-11d0-958A-006097C9A090}", ctypes.byref(clsid)) # TaskbarList
        ole32.CLSIDFromString("{EA1AFB91-9E28-4B86-90E9-9E9F8A5EEFAF}", ctypes.byref(iid)) # ITaskbarList3
        self.taskbar = ctypes.c_void_p()
        if ole32.CoCreateInstance(ctypes.byref(clsid), None, 1, ctypes.byref(iid), ctypes.byref(self.taskbar)) != 0:
            raise OSError("the taskbar interface isn't available")
        self.call(3) # HrInit

        size = user32.GetSystemMetrics(49) or 16 # SM_CXSMICON: the size Windows draws these buttons at
        self.icons = {name: self.makeIcon(name, size) for name in ("prev", "play", "pause", "next")}

        # Windows says when the taskbar button exists (and again if Explorer restarts); buttons can only be added then
        self.createdMessage = user32.RegisterWindowMessageW("TaskbarButtonCreated")
        WNDPROC = ctypes.WINFUNCTYPE(ctypes.c_ssize_t, wt.HWND, wt.UINT, wt.WPARAM, wt.LPARAM)
        user32.SetWindowLongPtrW.restype = ctypes.c_void_p
        user32.SetWindowLongPtrW.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p]
        user32.CallWindowProcW.restype = ctypes.c_ssize_t
        user32.CallWindowProcW.argtypes = [ctypes.c_void_p, wt.HWND, wt.UINT, wt.WPARAM, wt.LPARAM]
        self.proc = WNDPROC(self.onMessage) # kept, so it isn't garbage collected while Windows still calls it
        self.oldProc = user32.SetWindowLongPtrW(self.hwnd, -4, ctypes.cast(self.proc, ctypes.c_void_p)) # GWLP_WNDPROC

    def call(self, index, *args):
        """Calls method number `index` of the ITaskbarList3 interface (its place in the interface's method table)"""
        ctypes = self.ctypes
        table = ctypes.cast(self.taskbar, ctypes.POINTER(ctypes.POINTER(ctypes.c_void_p))).contents
        method = ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_void_p, *(type(a) for a in args))(table[index])
        return method(self.taskbar, *args)

    def makeIcon(self, name, size):
        """A white symbol drawn with PIL, turned into a Windows icon straight from its PNG bytes"""
        big = size * 4 # drawn large and scaled down, for smooth edges
        image = Image.new("RGBA", (big, big), (0, 0, 0, 0))
        draw = ImageDraw.Draw(image)
        u = big / 16
        if name == "play":
            draw.polygon([(4.5 * u, 3 * u), (4.5 * u, 13 * u), (13 * u, 8 * u)], fill="white")
        elif name == "pause":
            draw.rectangle([4 * u, 3 * u, 7 * u, 13 * u], fill="white")
            draw.rectangle([9 * u, 3 * u, 12 * u, 13 * u], fill="white")
        else: # prev and next: a bar and a triangle; next is prev mirrored
            draw.rectangle([3 * u, 3.5 * u, 5 * u, 12.5 * u], fill="white")
            draw.polygon([(13 * u, 3.5 * u), (13 * u, 12.5 * u), (5.5 * u, 8 * u)], fill="white")
            if name == "next":
                image = image.transpose(Image.FLIP_LEFT_RIGHT)
        png = io.BytesIO()
        image.resize((size, size), Image.LANCZOS).save(png, "PNG")
        data = png.getvalue()
        create = self.user32.CreateIconFromResourceEx
        create.restype = self.wt.HICON
        create.argtypes = [self.ctypes.c_char_p, self.wt.DWORD, self.wt.BOOL, self.wt.DWORD, self.ctypes.c_int,
                           self.ctypes.c_int, self.wt.UINT]
        return create(data, len(data), True, 0x00030000, size, size, 0)

    def buttons(self):
        play = ("pause", "Pause") if self.playing else ("play", "Play")
        array = (self.THUMBBUTTON * 3)()
        for button, (iid, (icon, tip)) in zip(array, ((self.PREV, ("prev", "Previous")), (self.PLAY, play),
                                                      (self.NEXT, ("next", "Next")))):
            button.dwMask = 0x2 | 0x4 | 0x8 # THB_ICON, THB_TOOLTIP, THB_FLAGS
            button.iId, button.hIcon, button.szTip, button.dwFlags = iid, self.icons[icon], T(tip), 0
        return array

    def add(self):
        array = self.buttons()
        self.added = self.call(15, self.wt.HWND(self.hwnd), self.wt.UINT(3), self.ctypes.c_void_p(self.ctypes.addressof(array))) == 0 # ThumbBarAddButtons

    def follow(self, root):
        """Tk swaps its frame window for a new one when full screen comes or goes, and the new one has a taskbar button of
        its own: its messages are caught too, and its preview gets the buttons once Windows says the button is there"""
        hwnd = self.user32.GetParent(root.winfo_id()) or root.winfo_id()
        if hwnd == self.hwnd:
            return
        self.hwnd, self.added = hwnd, False
        self.oldProc = self.user32.SetWindowLongPtrW(hwnd, -4, self.ctypes.cast(self.proc, self.ctypes.c_void_p))
        root.after(1000, lambda: self.added or hwnd != self.hwnd or self.add()) # in case that message came too early to be caught

    def setPlaying(self, playing):
        """Shows pause while something plays and play otherwise"""
        if playing != self.playing:
            self.playing = playing
            if self.added:
                array = self.buttons()
                self.call(16, self.wt.HWND(self.hwnd), self.wt.UINT(3), self.ctypes.c_void_p(self.ctypes.addressof(array))) # ThumbBarUpdateButtons

    def onMessage(self, hwnd, message, wparam, lparam):
        try:
            if message == self.WM_COMMAND and (wparam >> 16) & 0xFFFF == self.THBN_CLICKED:
                self.events.put(("thumb", wparam & 0xFFFF))
                return 0
            if message == self.createdMessage:
                self.events.put(("thumbReady",))
        except Exception:
            pass # never let a slip here stop the window from getting its messages
        return self.user32.CallWindowProcW(self.oldProc, hwnd, message, wparam, lparam)

# ---- audio --------------------------------------------------------------------------------------------------------
class Player:
    """Plays a queue of (label, path-or-url) through the PowerShell audio host. A background thread walks the queue and
    reports back through onState(state, value): ("playing", (label, path)), ("paused", bool), ("progress", (pos, duration)),
    ("vis", levels), ("idle", "") when the queue is done, and ("error", message)."""

    def __init__(self, onState, channel=1):
        """channel: 1 or 2. Each channel is its own audio process (and YouTube window), so both play at once. Only
        channel one shows in Windows' media controls"""
        self.onState = onState
        self.channel = channel
        self.volume = 800 # 0-1000
        self.muted = False
        self.eq = (0.0, 0.0, 0.0) # bass, mid, treble in dB
        self.fades = (1.5, 1.5) # fade-in and fade-out lengths in seconds
        self.paused = False
        self.shuffle = False # play the queue in random order
        self.loop = "off" # "off", "list" (wrap round at the end) or "one" (repeat the track)
        self._failed = False
        self._closed = False
        self._stop = threading.Event()
        self._thread = None
        self._proc = None
        self._lock = threading.Lock()
        self._lines = queue.Queue()
        self._trackId = 0
        self._pos = 0.0
        self._media = None # the last "media" command, sent again if the host restarts
        self.youtube = YouTubeBrowser() if channel == 1 else YouTubeBrowser(YT_PROFILE_DIR.with_name("youtube_player2"),
                                                                          YT_WINDOW_TITLE + " (2)") # the window YouTube songs play in
        self._onYouTube = False # the current track is a YouTube song: pause, seek and volume go to the browser
        self._ytToggled = 0.0 # when the app last paused or resumed the YouTube player

    def play(self, items, start=None):
        """items is a list of (label, path) played back to back, beginning at index start. Without a start, the first one,
        or a random one when shuffling"""
        self.stop(closeYouTube=False) # a YouTube song next reuses the open window; anything else closes it
        while not self._lines.empty(): # drop leftovers like a next press made while nothing was playing
            self._lines.get_nowait()
        self._stop = threading.Event()
        self._thread = threading.Thread(target=self._run, args=(items, start, self._stop), daemon=True)
        self._thread.start()

    def stop(self, closeYouTube=True):
        self._stop.set()
        self._lines.put(None) # wake the playback thread right away
        if self._thread and self._thread.is_alive() and self._thread is not threading.current_thread():
            self._thread.join(timeout=3)
        self._send("stop", spawn=False)
        if closeYouTube and self.youtube.isOpen():
            threading.Thread(target=self.youtube.close, daemon=True).start() # the window may take a moment to answer
        self._onYouTube = False
        self._setPaused(False)

    def togglePause(self):
        if self.isPlaying:
            self._setPaused(not self.paused)
            if self._onYouTube:
                self._lines.put("yt " + ("pauseVideo()" if self.paused else "playVideo()"))
                self._ytToggled = time.time() # until the page has it, the player still reports the old state
            else:
                self._send("pause" if self.paused else "resume", spawn=False)

    def _setPaused(self, paused):
        if self.paused != paused:
            self.paused = paused
            self.onState("paused", paused)

    @property
    def onYouTube(self):
        """The current song is a YouTube one, playing in the browser window"""
        return self._onYouTube

    @property
    def isPlaying(self):
        """True from play() until the queue finishes or stop() is called"""
        return bool(self._thread and self._thread.is_alive() and not self._stop.is_set())

    def next(self):
        self._lines.put("next")

    def previous(self):
        self._lines.put("prev")

    def seek(self, seconds):
        if self._onYouTube:
            self._lines.put(f"yt seekTo({seconds:.1f}, true)")
        else:
            self._send(f"seek {seconds:.1f}", spawn=False)

    def setVolume(self, volume):
        self.volume = int(float(volume))
        self._send(f"vol {self.volume / 1000}", spawn=False)
        if self._onYouTube:
            self._lines.put(f"yt setVolume({self.volume // 10})")

    def setEq(self, bass, mid, treble):
        self.eq = (bass, mid, treble)
        self._send(f"eq {bass:.1f} {mid:.1f} {treble:.1f}", spawn=False)

    def setFades(self, fadeIn, fadeOut):
        self.fades = (fadeIn, fadeOut)
        self._send(f"fade {fadeIn:.2f} {fadeOut:.2f}", spawn=False)

    def setShuffle(self, on):
        self.shuffle = on
        self._lines.put("reorder") # the playback thread re-deals what's left of the queue

    def _deal(self, count, first, played=()):
        """Order to play the queue in: shuffled (never repeating a song of `played`), or simply in sequence"""
        if not self.shuffle:
            return list(range(count))
        rest = [j for j in range(count) if j not in played and j != first]
        random.shuffle(rest)
        return list(played) + ([first] if first is not None and first not in played else []) + rest

    def warmUp(self):
        """Start the audio process ahead of time so the first track doesn't wait for PowerShell and the compile. Skipped
        once something already started it: the warm-up plays a moment of silence, which would replace a song"""
        with self._lock:
            started = self._proc is not None
        if not started:
            self._send("warm") # silent test run through the whole audio chain, queued behind the start-up settings

    def setMuted(self, muted):
        self.muted = muted
        self._send(f"mute {int(muted)}", spawn=False)
        if self._onYouTube:
            self._lines.put("yt " + ("mute()" if muted else "unMute()"))

    def close(self):
        self._closed = True # nothing may start the audio host again (a warm-up or a playing thread could still ask)
        self._stop.set()
        self.youtube.close()
        self._send("quit", spawn=False)
        with self._lock:
            if self._proc and self._proc.poll() is None:
                subprocess.run(["taskkill", "/F", "/T", "/PID", str(self._proc.pid)], creationflags=subprocess.CREATE_NO_WINDOW,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL) # the host and anything it started
                self._proc.kill()

    def _alive(self):
        return self._proc is not None and self._proc.poll() is None

    def _send(self, command, spawn=True):
        with self._lock:
            if self._closed:
                return
            if not self._alive():
                if not spawn:
                    return
                self._spawn()
            try:
                self._proc.stdin.write(command + "\n")
                self._proc.stdin.flush()
            except OSError:
                pass # player process just died, the next play() restarts it

    def _spawn(self):
        proc = subprocess.Popen(
            ["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-Command", HOST_SCRIPT],
            creationflags=subprocess.CREATE_NO_WINDOW, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL, text=True, env={**os.environ, "LETTUCE_ENGINE": str(resourcePath("audio_engine")),
                                                       "LETTUCE_SMTC": "1" if self.channel == 1 else "0"})
        threading.Thread(target=self._read, args=(proc,), daemon=True).start()
        self._proc = proc
        proc.stdin.write(f"vol {self.volume / 1000}\nmute {int(self.muted)}\neq {self.eq[0]:.1f} {self.eq[1]:.1f} {self.eq[2]:.1f}\nfade {self.fades[0]:.2f} {self.fades[1]:.2f}\n")
        if self._media:
            proc.stdin.write(self._media + "\n") # a restarted host shows the song in Windows' media controls again

    def _read(self, proc):
        """The host's output: presses from Windows' media controls go straight to the app, the rest to the playback thread"""
        for line in proc.stdout:
            line = line.strip()
            if line.startswith("button "):
                self.onState("button", line[7:])
            else:
                self._lines.put(line)

    def showInWindows(self, status, title):
        """What Windows' media controls show: "playing", "paused" or "stopped", and the song. Earbuds go by it"""
        self._media = "media %s %s" % (status, base64.b64encode(title.encode("utf-8")).decode("ascii"))
        self._send(self._media, spawn=False)

    def _run(self, items, start, stopEvent):
        """The playback thread: plays the queue in order (or shuffled), skipping missing files, until it runs out or stops"""
        count = len(items)
        if start is None:
            start = random.randrange(count) if self.shuffle and count else 0
        order = self._deal(count, start)
        k = order.index(start) if start in order else 0 # position in the play order
        playedThisPass = False # a list of nothing but broken tracks must not loop forever
        while not stopEvent.is_set():
            if k >= len(order) and self.loop == "list" and playedThisPass:
                order, k, playedThisPass = self._deal(count, None), 0, False
            if not 0 <= k < len(order):
                break
            label, path = items[order[k]]
            if "://" not in str(path) and not Path(path).is_file():
                self.onState("error", f'"{label}" is missing from {Path(path).parent}. Move it back there or remove it from the library.')
                k += 1
                continue
            self._trackId += 1
            trackId = str(self._trackId)
            self._pos = 0.0
            self._setPaused(False) # a new track always starts playing
            self.onState("playing", (label, path))
            self._onYouTube = isYouTube(path)
            if self._onYouTube:
                self._send("stop", spawn=False) # the file before it, if one was playing
            else:
                if self.youtube.isOpen():
                    self.youtube.close() # YouTube's done for now
                self._send(f"play {trackId} {path if '://' in str(path) else Path(path).resolve().as_uri()}")
            self._failed = False
            while True:
                if self._onYouTube:
                    self._send("listen 1") # the browser plays it, so the visualizer listens to the speakers
                    try:
                        step = self._waitForYouTube(str(path), stopEvent, k, len(order))
                    finally:
                        self._send("listen 0", spawn=False)
                else:
                    step = self._waitForTrack(trackId, stopEvent, k, len(order))
                if step != "reorder":
                    break
                if self.shuffle: # keep what's been played and the current song, shuffle the rest
                    order = self._deal(count, order[k], order[:k + 1])
                else: # back to the library's own order, carrying on from the current song
                    order, k = list(range(count)), order[k]
            if step == "closed": # the YouTube window was closed by hand: that stops the music
                self._onYouTube = False
                self.onState("idle", "")
                return
            if step is None:
                return
            playedThisPass = playedThisPass or not self._failed
            k += step
        if not stopEvent.is_set():
            self._onYouTube = False
            self.youtube.close()
            self.onState("idle", "")

    def _waitForTrack(self, trackId, stopEvent, i, count):
        """Blocks until the track should change. Returns the index step (1 next, -1 previous) or None to give up"""
        while not stopEvent.is_set():
            try:
                line = self._lines.get(timeout=1)
            except queue.Empty:
                if not self._alive():
                    self.onState("error", "Player process stopped unexpectedly")
                    return None
                continue
            if line == "reorder":
                return "reorder"
            if line == f"ended {trackId}":
                return 0 if self.loop == "one" else 1
            if line and line.startswith(f"failed {trackId} "):
                reason = line.split(" ", 2)[2].split(" (Exception")[0].strip()
                self.onState("error", f"Can't play this track: {reason}")
                self._failed = True
                return 1
            if line == "next" and (i + 1 < count or self.loop == "list"):
                return 1
            if line == "prev":
                if self._pos > 3 or i == 0:
                    self.seek(0) # like most players: first press restarts the track
                else:
                    return -1
            elif line and line.startswith(f"pos {trackId} "):
                _, _, pos, dur = line.split()
                self._pos = float(pos)
                self.onState("progress", (self._pos, float(dur)))
            elif line and line.startswith("vis "):
                self.onState("vis", [float(v) for v in line.split()[1:]])
        return 0

    def _waitForYouTube(self, url, stopEvent, i, count):
        """_waitForTrack for a YouTube song: opens it in the browser window, then follows YouTube's player there twice
        a second for its progress and its end. Returns the index step, "reorder", or "closed" when the window is shut"""
        try:
            self.youtube.open(url)
        except Exception as e:
            self.onState("error", f"Can't play this YouTube song: {e}")
            self._failed = True
            return 1
        wanted, opened, started, nudged, polled = youTubeId(url), time.time(), False, False, 0.0
        minimized = False # each song puts the window away again, even after it was opened by hand
        while not stopEvent.is_set():
            try:
                line = self._lines.get(timeout=0.25)
            except queue.Empty:
                line = ""
            # once the song is playing: YouTube's player won't start in a window that was minimized before its page loaded
            # (a song loaded into the minimized window after that plays fine, so it then stays down from one song to the next)
            if started and not minimized:
                minimized = self.youtube.minimize()
            if line == "reorder":
                return "reorder"
            if line == "next" and (i + 1 < count or self.loop == "list"):
                return 1
            if line == "prev":
                if self._pos > 3 or i == 0:
                    self.youtube.control("seekTo(0, true)")
                else:
                    return -1
            elif line and line.startswith("yt "): # pause, seek, volume from the app's buttons
                self.youtube.control(line[3:])
            elif line and line.startswith("vis "): # what the speakers are playing
                self.onState("vis", [float(v) for v in line.split()[1:]])
            if time.time() - polled < 0.5:
                continue
            polled = time.time()
            try:
                state = self.youtube.state()
            except YouTubeClosed:
                return "closed"
            if state and state["error"] and state["want"] == wanted: # not one left over from the video before
                self.onState("error", "Can't play this YouTube song. " + YT_ERRORS.get(state["error"], f"YouTube error {state['error']}."))
                self._failed = True
                return 1
            if state and state["ad"]:
                opened = time.time() # adverts aren't the song: wait them out, however long they are
            elif state and state["id"] == wanted:
                if not started:
                    started = True
                    self.youtube.control(f"setVolume({self.volume // 10})")
                    self.youtube.control("mute()" if self.muted else "unMute()")
                if state["state"] == 0:
                    return 0 if self.loop == "one" else 1
                if state["state"] in (1, 2) and self.paused != (state["state"] == 2) and time.time() - self._ytToggled > 2:
                    self._setPaused(state["state"] == 2) # paused or played in the browser itself
                self._pos = state["time"]
                self.onState("progress", (state["time"], state["duration"]))
            elif started and state and state["id"] and state["id"] != wanted:
                return 1 # YouTube's autoplay went on to another video, so this one is over
            elif not started and not nudged and time.time() - opened > 8:
                nudged = True
                self.youtube.control("playVideo()") # the browser held back autoplay
            elif not started and time.time() - opened > 45:
                self.onState("error", "YouTube didn't start this video. It may be unavailable in your country or need a sign-in.")
                self._failed = True
                return 1
        return 0

# ---- songs and playlist files -------------------------------------------------------------------------------------
def getAllSongs(libraryPaths=()):
    """Songs in User_Music plus the dropped-in files, wherever they live (they may be missing from disk)"""
    songs = []
    if songFolderPath.is_dir():
        songs = [(f.stem, f) for f in songFolderPath.iterdir() if f.is_file() and f.suffix.lower() in SONG_SUFFIXES]
    known = {os.path.normcase(str(f)) for _, f in songs}
    for p in libraryPaths:
        if os.path.normcase(p) not in known:
            known.add(os.path.normcase(p))
            songs.append((Path(p).stem, Path(p)))
    songs = [s for s in songs if s[0].lower() != HIDDEN_SONG] # only the voice command "rick" plays it
    return sorted(songs, key=lambda s: s[0].lower())

def parsePlaylist(playlistPath):
    """(label, path) for every track in an .xspf playlist file"""
    ns = {"x": "http://xspf.org/ns/0/"}
    paths = []
    for t in ET.parse(playlistPath).getroot().findall(".//x:track/x:location", ns):
        if not t.text:
            continue
        parsed = urlparse(t.text)
        path = unquote(parsed.path).lstrip("/").replace("/", "\\") if parsed.scheme == "file" else t.text
        paths.append((Path(path).stem if parsed.scheme == "file" else path, path))
    return paths

# ---- colour and picture helpers -------------------------------------------------------------------------------
def hexToRgb(color):
    return tuple(int(color[i:i + 2], 16) for i in (1, 3, 5))

def lighten(color, amount):
    return tuple(round(c + (255 - c) * amount) for c in hexToRgb(color))

def onAccent(color):
    """Dark text on light accents, white text on dark ones"""
    r, g, b = hexToRgb(color)
    return "#0b0d12" if (0.299 * r + 0.587 * g + 0.114 * b) / 255 > 0.5 else "#ffffff"

def setAccent(color):
    global ACCENT
    ACCENT = color

def voiceInstalled():
    """Voice control is an optional part of the install: the speech model and Vosk's library, about 120 MB"""
    if not (resourcePath(VOSK_DIR) / "am").is_dir():
        return False
    if getattr(sys, "frozen", False): # the built app: Vosk's code is always in it, its library only with voice
        return (Path(sys._MEIPASS) / "vosk" / "libvosk.dll").is_file()
    import importlib.util
    return importlib.util.find_spec("vosk") is not None

def resourcePath(name):
    """Bundled files live in PyInstaller's temp folder, loose ones next to the script/exe"""
    bundled = Path(getattr(sys, "_MEIPASS", BASE_DIR)) / name
    return bundled if bundled.exists() else BASE_DIR / name

def findBackground():
    """First .jpg in the assets folder, else the first .png"""
    if not ASSETS_DIR.is_dir():
        return None
    for suffixes in ((".jpg", ".jpeg"), (".png",)):
        for f in sorted(ASSETS_DIR.iterdir()):
            if f.is_file() and f.suffix.lower() in suffixes:
                return f
    return None

# ---- drawing helpers ---------------------------------------------------------------------------------------------
GIF_FRAMES, GIF_BYTES = 400, 200 * 1024 * 1024 # most frames kept, and the most memory they may take at the picture's size

def loadBackground(chosen=""):
    """The picture picked in Settings, or else the first .jpg/.png in the assets folder. An animated one (a .gif) is its first
    frame, with every frame and how long it shows in .animation: [(frame, milliseconds), ...]"""
    path = Path(chosen) if chosen and Path(chosen).is_file() else findBackground()
    if not path:
        return None
    try:
        with Image.open(path) as picture:
            count = min(getattr(picture, "n_frames", 1), GIF_FRAMES)
            # plenty for any window and much cheaper to rescale; many frames are kept smaller still, to fit in memory
            pixels = min(1920 * 1080, GIF_BYTES // (3 * count))
            scale = min(1.0, (pixels / (picture.width * picture.height)) ** 0.5)
            size = (max(int(picture.width * scale), 1), max(int(picture.height * scale), 1))
            frames = []
            for i in range(count):
                picture.seek(i)
                delay = picture.info.get("duration") or 100
                frames.append((picture.convert("RGB").resize(size, Image.BILINEAR) if scale < 1 else picture.convert("RGB"),
                               int(delay) if delay > 10 else 100)) # like browsers: a near-zero delay means 0.1 s
    except (OSError, ValueError, EOFError):
        return None
    return withAnimation(frames[0][0], frames)

def loadCover(data):
    """A song's cover (picture bytes from readArt) as a background, or None when it can't be read"""
    try:
        with Image.open(io.BytesIO(data)) as picture:
            return withAnimation(picture.convert("RGB"), [])
    except Exception:
        return None

def withAnimation(image, frames):
    image.animation = frames if len(frames) > 1 else None
    return image

def isNightHour(hour):
    """Night runs from 9 PM until 7 AM"""
    return hour >= 21 or hour < 7

def loadNightBackground(chosen, day):
    """The night picture picked in Settings, or else the day picture darkened and tinted blue"""
    if chosen and Path(chosen).is_file():
        image = loadBackground(chosen)
        if image:
            return image
    image = loadBackground(day)
    if image is None:
        return None
    tint = Image.new("RGB", image.size, (8, 12, 36))
    frames = [(Image.blend(frame, tint, 0.62), delay) for frame, delay in image.animation or [(image, 0)]]
    return withAnimation(frames[0][0], frames)

def roundedShape(width, height, fill, outline=None, radius=None):
    """Anti-aliased rounded rectangle with real transparency (a pill when radius is None)"""
    width, height = max(int(width), 2), max(int(height), 2)
    scale = 4 if width * height < 60000 else 2 # big panels: less supersampling keeps resizing quick
    big = Image.new("RGBA", (width * scale, height * scale), (0, 0, 0, 0))
    radius = min(width, height) // 2 if radius is None else radius
    ImageDraw.Draw(big).rounded_rectangle(
        (0, 0, width * scale - 1, height * scale - 1), radius=radius * scale,
        fill=fill, outline=outline, width=2 * scale if outline else 0)
    return big.resize((width, height), Image.LANCZOS)

def roundedImage(width, height, fill, outline=None, radius=None):
    return ImageTk.PhotoImage(roundedShape(width, height, fill, outline, radius))

def roundedMask(width, height, radius, inset=0):
    """Single-channel anti-aliased rounded rectangle, much cheaper to make than an RGBA one"""
    scale = 4 if width * height < 60000 else 2
    mask = Image.new("L", (width * scale, height * scale), 0)
    ImageDraw.Draw(mask).rounded_rectangle(
        (inset * scale, inset * scale, (width - inset) * scale - 1, (height - inset) * scale - 1),
        radius=max(radius - inset, 0) * scale, fill=255)
    return mask.resize((width, height), Image.BOX)

def frostedImage(blurred, x, y, width, height, radius=20, alpha=195):
    """Panel made of the blurred, darkened background behind it, so text stays readable over any picture"""
    outer = roundedMask(width, height, radius)
    border = ImageChops.subtract(outer, roundedMask(width, height, radius, inset=1)).point(lambda v: v * 70 // 255)
    if blurred is None:
        panel = Image.new("RGBA", (width, height), (12, 14, 20, 255))
        panel.putalpha(outer.point(lambda v: v * 120 // 255))
    else:
        panel = blurred.crop((int(x), int(y), int(x) + width, int(y) + height)).convert("RGBA")
        panel = Image.blend(panel, Image.new("RGBA", panel.size, (12, 14, 20, 255)), 0.40)
        panel.putalpha(outer.point(lambda v: v * alpha // 255))
    edge = Image.new("RGBA", (width, height), (255, 255, 255, 0))
    edge.putalpha(border)
    return ImageTk.PhotoImage(Image.alpha_composite(panel, edge))

def fillMonitor(root):
    """Read before going full screen: a function that stretches the full screen window over the monitor the window is on
    now. Tk's full screen always takes the main monitor, so a window on a second one would jump across"""
    import ctypes
    from ctypes import wintypes as wt
    user32 = ctypes.WinDLL("user32") # its own copy, so the types set here don't leak out
    handle = ctypes.c_void_p
    for function, result, args in ((user32.GetParent, handle, [handle]), (user32.MonitorFromWindow, handle, [handle, wt.DWORD]),
                                   (user32.GetMonitorInfoW, wt.BOOL, [handle, handle]),
                                   (user32.SetWindowPos, wt.BOOL, [handle, handle] + [ctypes.c_int] * 4 + [wt.UINT])):
        function.restype, function.argtypes = result, args

    class MONITORINFO(ctypes.Structure):
        _fields_ = [("cbSize", wt.DWORD), ("rcMonitor", wt.RECT), ("rcWork", wt.RECT), ("dwFlags", wt.DWORD)]

    frame = lambda: user32.GetParent(root.winfo_id()) or root.winfo_id() # the real window around Tk's
    info = MONITORINFO(cbSize=ctypes.sizeof(MONITORINFO))
    if not user32.GetMonitorInfoW(user32.MonitorFromWindow(frame(), 2), ctypes.byref(info)): # 2: the nearest monitor
        return None
    box = info.rcMonitor
    # the frame is looked up again when it's used: going full screen makes Tk replace it with a new one
    return lambda: user32.SetWindowPos(frame(), None, box.left, box.top, box.right - box.left, box.bottom - box.top,
                                       0x0014) # SWP_NOZORDER | SWP_NOACTIVATE

def tintTitleBar(window, color):
    """Colours a window's title bar (the strip with minimize, maximize and close) and its edge, with the title in the
    colour that reads on it. Windows 11 only: older Windows keep their own colours"""
    import ctypes
    user32, dwmapi = ctypes.WinDLL("user32"), ctypes.WinDLL("dwmapi") # own copies, so the types set here don't leak out
    user32.GetParent.restype, user32.GetParent.argtypes = ctypes.c_void_p, [ctypes.c_void_p]
    dwmapi.DwmSetWindowAttribute.argtypes = [ctypes.c_void_p, ctypes.c_uint, ctypes.c_void_p, ctypes.c_uint]
    window.update_idletasks() # so the frame window exists
    frame = user32.GetParent(window.winfo_id()) or window.winfo_id() # the real window around Tk's
    # DWMWA_BORDER_COLOR, DWMWA_CAPTION_COLOR, DWMWA_TEXT_COLOR; colours are 0x00BBGGRR
    for attribute, value in ((34, color), (35, color), (36, onAccent(color))):
        r, g, b = hexToRgb(value)
        value = ctypes.c_uint(r | g << 8 | b << 16)
        dwmapi.DwmSetWindowAttribute(frame, attribute, ctypes.byref(value), ctypes.sizeof(value))

def captureWindow(widget):
    """A picture of what the widget shows. It is read from Windows' own copy of the window, so whatever is in front of
    it (other windows, the weather) isn't in it. None when Windows can't give one"""
    import ctypes
    from ctypes import wintypes as wt
    user32, gdi32 = ctypes.WinDLL("user32"), ctypes.WinDLL("gdi32") # own copies, so the types set here don't leak out
    handle = ctypes.c_void_p
    for function, result, args in (
            (user32.GetParent, handle, [handle]), (user32.GetDC, handle, [handle]),
            (user32.ReleaseDC, ctypes.c_int, [handle, handle]), (user32.GetClientRect, wt.BOOL, [handle, handle]),
            (user32.ClientToScreen, wt.BOOL, [handle, handle]), (user32.PrintWindow, wt.BOOL, [handle, handle, wt.UINT]),
            (gdi32.CreateCompatibleDC, handle, [handle]),
            (gdi32.CreateCompatibleBitmap, handle, [handle, ctypes.c_int, ctypes.c_int]),
            (gdi32.SelectObject, handle, [handle, handle]),
            (gdi32.GetDIBits, ctypes.c_int, [handle, handle, wt.UINT, wt.UINT, handle, handle, wt.UINT]),
            (gdi32.DeleteObject, wt.BOOL, [handle]), (gdi32.DeleteDC, wt.BOOL, [handle])):
        function.restype, function.argtypes = result, args

    class Header(ctypes.Structure): # BITMAPINFO, with room for the colour table it doesn't need
        _fields_ = [("size", wt.DWORD), ("width", wt.LONG), ("height", wt.LONG), ("planes", wt.WORD), ("bits", wt.WORD),
                    ("compression", wt.DWORD), ("rest", wt.DWORD * 9)]

    inner = widget.winfo_toplevel().winfo_id()
    frame = user32.GetParent(inner) or inner # the real window around Tk's
    rect, origin = wt.RECT(), wt.POINT(0, 0)
    user32.GetClientRect(frame, ctypes.byref(rect))
    user32.ClientToScreen(frame, ctypes.byref(origin))
    w, h = rect.right, rect.bottom
    if w <= 0 or h <= 0:
        return None
    screen = user32.GetDC(None)
    dc = gdi32.CreateCompatibleDC(screen)
    bitmap = gdi32.CreateCompatibleBitmap(screen, w, h)
    old = gdi32.SelectObject(dc, bitmap)
    ok = user32.PrintWindow(frame, dc, 3) # PW_CLIENTONLY | PW_RENDERFULLCONTENT
    gdi32.SelectObject(dc, old)
    header = Header(40, w, -h, 1, 32, 0) # negative height: rows top to bottom
    pixels = ctypes.create_string_buffer(w * h * 4)
    rows = gdi32.GetDIBits(dc, bitmap, 0, h, pixels, ctypes.byref(header), 0)
    gdi32.DeleteObject(bitmap)
    gdi32.DeleteDC(dc)
    user32.ReleaseDC(None, screen)
    if not ok or rows != h:
        return None
    image = Image.frombuffer("RGB", (w, h), pixels.raw, "raw", "BGRX", 0, 1)
    x, y = widget.winfo_rootx() - origin.x, widget.winfo_rooty() - origin.y
    return image.crop((x, y, x + widget.winfo_width(), y + widget.winfo_height()))

# ---- canvas widgets ----------------------------------------------------------------------------------------------
# Everything is drawn on one canvas over the background picture, because native tkinter widgets can't be see-through.
# Each widget tags its items with the tab it belongs to ("tab_library"...), so a whole tab shows or hides in one call.

class GlassButton:
    """Pill-shaped, semi-transparent button drawn on the canvas so the background shows through"""
    LOOKS = { # fill, outline, text colour
        "normal": ((255, 255, 255, 36), (255, 255, 255, 80), TEXT),
        "on": ((62, 207, 142, 200), (150, 235, 195, 235), "#0b0d12"),
        "danger": ((255, 107, 107, 205), (255, 170, 170, 235), "#0b0d12"),
    }
    STYLES = {"TButton": "normal", "Accent.TButton": "accent", "On.TButton": "on", "Danger.TButton": "danger"}
    instances = [] # every button, so a theme change can repaint them all

    def __init__(self, canvas, text, command, look="normal", group="", size=10, family=FONT):
        GlassButton.instances.append(self)
        self.canvas, self.text, self.command, self.look = canvas, T(text), command, look
        self.state = "idle"
        self.size = (0, 0)
        self.photos = {}
        tag = f"button{id(self)}"
        tags = (tag, group) if group else (tag,)
        self.image = canvas.create_image(0, 0, anchor="nw", tags=tags)
        self.caption = canvas.create_text(0, 0, text=self.text, font=(family, size, "bold"), tags=tags)
        canvas.tag_bind(tag, "<Enter>", lambda e: self.setState("hover"))
        canvas.tag_bind(tag, "<Leave>", lambda e: self.setState("idle"))
        canvas.tag_bind(tag, "<ButtonPress-1>", lambda e: self.setState("down"))
        canvas.tag_bind(tag, "<ButtonRelease-1>", self.onRelease)

    def setState(self, state):
        self.state = state
        self.canvas.configure(cursor="hand2" if state != "idle" else "")
        self.draw()

    def onRelease(self, event):
        wasDown = self.state == "down"
        self.setState("hover")
        if wasDown:
            self.command()

    def configure(self, text=None, style=None):
        if text is not None:
            self.text = T(text)
        if style is not None:
            self.look = self.STYLES[style]
            self.photos = {}
        self.draw()

    def colors(self):
        if self.look == "accent": # follows the theme colour
            return (hexToRgb(ACCENT) + (200,), lighten(ACCENT, 0.4) + (235,), onAccent(ACCENT))
        return self.LOOKS[self.look]

    def repaint(self):
        self.photos = {}
        try:
            self.draw()
        except tk.TclError:
            pass # its window is already gone

    def photo(self):
        if self.state not in self.photos and min(self.size) > 1:
            fill, outline, _ = self.colors()
            boost = {"idle": 0, "hover": 34, "down": 70}[self.state]
            self.photos[self.state] = roundedImage(*self.size, fill[:3] + (min(255, fill[3] + boost),), outline)
        return self.photos.get(self.state)

    def draw(self):
        photo = self.photo()
        if photo:
            self.canvas.itemconfigure(self.image, image=photo)
        self.canvas.itemconfigure(self.caption, text=self.text, fill=self.colors()[2])

    def place(self, x, y, w, h):
        if (int(w), int(h)) != self.size:
            self.size, self.photos = (int(w), int(h)), {}
        self.canvas.coords(self.image, x, y)
        self.canvas.coords(self.caption, x + w / 2, y + h / 2)
        self.draw()

class GlassLabel:
    """Plain text on the canvas"""

    def __init__(self, canvas, text="", size=10, bold=False, color=TEXT, anchor="nw", group="", translate=True):
        """translate: False for a song's name, which is never translated"""
        self.canvas, self.translate = canvas, translate
        self.item = canvas.create_text(
            0, 0, text=T(text) if translate else text, fill=color, anchor=anchor, font=(FONT, size, "bold" if bold else "normal"),
            tags=(group,) if group else ())

    def configure(self, text=None, foreground=None):
        if text is not None:
            self.canvas.itemconfigure(self.item, text=T(text) if self.translate else text)
        if foreground is not None:
            self.canvas.itemconfigure(self.item, fill=foreground)

    def place(self, x, y, width=0):
        self.canvas.coords(self.item, x, y)
        self.canvas.itemconfigure(self.item, width=width)

class GlassCheck:
    """Tick box with a label, drawn on the canvas. It follows the theme colour"""
    instances = []

    def __init__(self, canvas, text, command, group=""):
        GlassCheck.instances.append(self)
        self.canvas, self.on, self.photo, self.command = canvas, False, None, command
        tag = f"check{id(self)}"
        tags = (group, tag) if group else (tag,)
        self.box = canvas.create_image(0, 0, anchor="nw", tags=tags)
        self.tick = canvas.create_text(0, 0, text="", font=(FONT, 11, "bold"), tags=tags)
        self.label = GlassLabel(canvas, text, 10, anchor="w", group=group)
        canvas.addtag_withtag(tag, self.label.item)
        canvas.tag_bind(tag, "<ButtonRelease-1>", lambda e: self.command())
        canvas.tag_bind(tag, "<Enter>", lambda e: canvas.configure(cursor="hand2"))
        canvas.tag_bind(tag, "<Leave>", lambda e: canvas.configure(cursor=""))

    def set(self, on):
        self.on = on
        self.draw()

    def draw(self):
        fill, outline = (hexToRgb(ACCENT) + (220,), lighten(ACCENT, 0.4) + (235,)) if self.on else ((255, 255, 255, 30), (255, 255, 255, 110))
        self.photo = roundedImage(22, 22, fill, outline, radius=6)
        self.canvas.itemconfigure(self.box, image=self.photo)
        self.canvas.itemconfigure(self.tick, text="✓" if self.on else "", fill=onAccent(ACCENT))

    def place(self, x, y):
        self.canvas.coords(self.box, x, y + 6)
        self.canvas.coords(self.tick, x + 11, y + 17)
        self.label.place(x + 32, y + 17)

class GlassSlider:
    """Rounded slider with the same set/get/configure(to=) feel as a ttk.Scale"""
    PAD = 9
    instances = []

    def __init__(self, canvas, low=0, high=1, command=None, onPress=None, onRelease=None, group=""):
        GlassSlider.instances.append(self)
        self.canvas, self.low, self.high = canvas, low, high
        self.command, self.onPress, self.onRelease = command, onPress, onRelease
        self.value = low
        self.box = (0, 0, 0, 0)
        self.hitPhoto = None
        tag = f"slider{id(self)}"
        tags = (tag, group) if group else (tag,)
        self.hit = canvas.create_image(0, 0, anchor="nw", tags=tags) # invisible, only makes the whole row clickable
        self.track = canvas.create_line(0, 0, 0, 0, width=6, capstyle="round", fill="#566074", tags=tags)
        self.fill = canvas.create_line(0, 0, 0, 0, width=6, capstyle="round", fill=ACCENT, tags=tags)
        self.knob = canvas.create_oval(0, 0, 0, 0, fill="#ffffff", outline="", tags=tags)
        canvas.tag_bind(tag, "<ButtonPress-1>", self.onDown)
        canvas.tag_bind(tag, "<B1-Motion>", self.onDrag)
        canvas.tag_bind(tag, "<ButtonRelease-1>", self.onUp)

    def get(self):
        return self.value

    def set(self, value):
        self.value = min(max(float(value), self.low), self.high)
        self.update()

    def configure(self, to=None):
        if to is not None:
            self.high = max(to, self.low + 0.001)
            self.set(self.value)

    def place(self, x, y, w, h=22):
        self.box = (x, y, w, h)
        self.hitPhoto = ImageTk.PhotoImage(Image.new("RGBA", (max(int(w), 1), int(h)), (0, 0, 0, 2)))
        self.canvas.itemconfigure(self.hit, image=self.hitPhoto)
        self.canvas.coords(self.hit, x, y)
        self.update()

    def update(self):
        x, y, w, h = self.box
        left, right, mid = x + self.PAD, x + w - self.PAD, y + h / 2
        position = left + (right - left) * (self.value - self.low) / (self.high - self.low)
        self.canvas.coords(self.track, left, mid, right, mid)
        self.canvas.coords(self.fill, left, mid, position, mid)
        self.canvas.coords(self.knob, position - 7, mid - 7, position + 7, mid + 7)

    def moveTo(self, event):
        x, _, w, _ = self.box
        fraction = (event.x - x - self.PAD) / max(w - 2 * self.PAD, 1)
        self.set(self.low + min(max(fraction, 0), 1) * (self.high - self.low))
        if self.command:
            self.command(self.value)

    def onDown(self, event):
        if self.onPress:
            self.onPress()
        self.moveTo(event)

    def onDrag(self, event):
        self.moveTo(event)

    def onUp(self, event):
        if self.onRelease:
            self.onRelease()

class GlassList:
    """Scrollable list drawn on the canvas so the picture shows through it (a tk.Listbox can't be transparent)"""
    instances = []
    ROW = 26

    def __init__(self, canvas, group="", size=10, onActivate=None, onDelete=None, onMove=None, onMoved=None,
                 onSelect=None, onMenu=None, handCursor=False, multi=False, onActivate2=None):
        """onActivate: double-click / Enter. onDelete: the Delete key. onMove(old, new) while dragging a row and onMoved()
        when the drag ends (reorderable lists only). onSelect: the selection changed. onMenu(event): right-click on a row.
        multi: Ctrl-click adds or removes a row, Shift-click selects a range, Ctrl+A selects everything.
        onActivate2: middle-click / Shift+Enter, which plays the row on the second channel"""
        GlassList.instances.append(self)
        self.canvas, self.group = canvas, group
        self.onActivate, self.onDelete, self.onMove, self.onMoved = onActivate, onDelete, onMove, onMoved
        self.onSelect, self.onMenu = onSelect, onMenu
        self.onActivate2 = onActivate2
        self.multi = multi
        self.marked = set() # every selected row while more than one is selected (empty otherwise: `selected` is the only one)
        self.anchor = None # where a Shift-click range starts
        self.font = tkfont.Font(family=FONT, size=size)
        self.items, self.selected, self.top = [], None, 0
        self.breaks = set() # rows that start a new group (an album), drawn with a line above them
        self.box, self.rows = (0, 0, 0, 0), 1
        self.dragFrom, self.dragMoved, self.drawPending = None, False, False
        self.photos = {}
        self.tag = f"list{id(self)}"
        self.tags = (self.tag, group) if group else (self.tag,)
        self.back = canvas.create_image(0, 0, anchor="nw", tags=self.tags) # translucent box, also catches the mouse
        self.highlights = [] # one coloured bar per visible row, shown behind the rows that are selected
        barTags = (group, f"bar{id(self)}") if group else (f"bar{id(self)}",) # the scroll bar is not part of the list: clicks on it don't pick rows
        self.thumb = canvas.create_line(-9999, -9999, -9999, -9999, width=4, capstyle="round", fill="#8a90a0", tags=barTags)
        self.barHit = canvas.create_image(-9999, -9999, anchor="nw", tags=barTags) # invisible strip along the right edge to grab
        self.barPhoto, self.barGeom, self.barGrab, self.barBusy = None, None, 0, False
        self.texts = []
        self.dividers = [] # one line per visible row, shown above the rows in `breaks`
        bar = barTags[-1]
        canvas.tag_bind(bar, "<ButtonPress-1>", self.onBarPress)
        canvas.tag_bind(bar, "<B1-Motion>", self.onBarDrag)
        canvas.tag_bind(bar, "<ButtonRelease-1>", self.onBarRelease)
        canvas.tag_bind(bar, "<Enter>", lambda e: self.showBar(True))
        canvas.tag_bind(bar, "<Leave>", lambda e: self.showBar(self.barBusy))
        canvas.tag_bind(self.tag, "<ButtonPress-1>", self.onPress)
        canvas.tag_bind(self.tag, "<B1-Motion>", self.onDrag)
        canvas.tag_bind(self.tag, "<ButtonRelease-1>", self.onRelease)
        canvas.tag_bind(self.tag, "<Double-Button-1>", self.onDouble)
        canvas.tag_bind(self.tag, "<Button-3>", self.onRightClick)
        canvas.tag_bind(self.tag, "<Button-2>", self.onMiddleClick)
        if handCursor:
            canvas.tag_bind(self.tag, "<Motion>", self.onMotion)
            canvas.tag_bind(self.tag, "<Leave>", lambda e: canvas.configure(cursor=""))

    # --- the bits of the Listbox API the app already uses
    def curselection(self):
        return () if self.selected is None else (self.selected,)

    def selection_set(self, index):
        self.select(index)

    def indices(self):
        """Every selected row, in order"""
        if self.marked:
            return sorted(self.marked)
        return [] if self.selected is None else [self.selected]

    def selectAll(self):
        if self.multi and self.items:
            self.marked = set(range(len(self.items)))
            self.queueDraw()
            if self.onSelect:
                self.onSelect()

    def selection_clear(self, first=0, last=None):
        self.selected, self.marked = None, set()
        self.queueDraw()

    def delete(self, first=0, last=None):
        self.items, self.selected, self.top = [], None, 0
        self.marked, self.anchor, self.breaks = set(), None, set()
        self.queueDraw()

    def insert(self, index, text):
        self.items.append(text)
        self.queueDraw()

    def see(self, index):
        if index < self.top:
            self.top = index
        elif index >= self.top + self.rows:
            self.top = index - self.rows + 1
        self.queueDraw()

    def nearest(self, y):
        _, by, _, _ = self.box
        return min(max(self.top + int((y - by - 6) // self.ROW), 0), max(len(self.items) - 1, 0))

    # --- behaviour
    def select(self, index):
        if 0 <= index < len(self.items):
            self.selected, self.anchor, self.marked = index, index, set()
            self.see(index)
            self.queueDraw()
            if self.onSelect:
                self.onSelect()

    def onMotion(self, event):
        _, by, _, _ = self.box
        row = int((event.y - by - 6) // self.ROW)
        over = 0 <= row < self.rows and self.top + row < len(self.items)
        self.canvas.configure(cursor="hand2" if over else "")

    def contains(self, x, y):
        bx, by, bw, bh = self.box
        return bx <= x <= bx + bw and by <= y <= by + bh

    def scroll(self, rows):
        self.top = min(max(self.top + rows, 0), max(len(self.items) - self.rows, 0))
        self.queueDraw()

    def moveItem(self, old, new):
        self.items.insert(new, self.items.pop(old))
        self.selected, self.breaks = new, set() # a hand-made order has no albums to mark
        self.queueDraw()

    def onPress(self, event):
        self.canvas.focus_set()
        index = self.nearest(event.y)
        if not self.items:
            return
        if self.multi and event.state & 0x4: # Ctrl: add this row to the selection, or take it out
            chosen = set(self.indices()) ^ {index}
            self.setChosen(chosen, index if index in chosen else None)
            self.anchor = index
        elif self.multi and event.state & 0x1 and self.anchor is not None: # Shift: everything from the anchor to here
            low, high = sorted((self.anchor, index))
            self.setChosen(set(range(low, high + 1)), index)
        else:
            self.select(index)
            self.dragFrom, self.dragMoved = index, False

    def setChosen(self, chosen, focus):
        """Selects exactly these rows. One row (or none) is the ordinary single selection"""
        self.selected = focus if focus is not None else (min(chosen) if chosen else None)
        self.marked = chosen if len(chosen) > 1 else set()
        self.queueDraw()
        if self.onSelect:
            self.onSelect()

    def onDrag(self, event):
        if self.onMove and self.dragFrom is not None and self.items:
            target = self.nearest(event.y)
            if target != self.dragFrom:
                self.moveItem(self.dragFrom, target)
                self.onMove(self.dragFrom, target)
                self.dragFrom, self.dragMoved = target, True

    def onRelease(self, event):
        if self.dragMoved and self.onMoved:
            self.onMoved()
        self.dragFrom, self.dragMoved = None, False

    def onDouble(self, event):
        if self.selected is not None and self.onActivate:
            self.onActivate()

    def onMiddleClick(self, event):
        """Plays the row under the pointer on the second channel"""
        _, by, _, _ = self.box
        row = int((event.y - by - 6) // self.ROW)
        index = self.top + row
        if self.onActivate2 and 0 <= row < self.rows and index < len(self.items):
            self.canvas.focus_set()
            self.select(index)
            self.onActivate2()

    def activate(self, second=False):
        """Enter plays the selected row; Shift+Enter plays it on the second channel"""
        if self.selected is not None:
            action = self.onActivate2 if second else self.onActivate
            if action:
                action()

    def onRightClick(self, event):
        """Opens the menu for the row under the pointer. Right-clicking inside a multiple selection keeps it"""
        _, by, _, _ = self.box
        row = int((event.y - by - 6) // self.ROW)
        index = self.top + row
        if self.onMenu and 0 <= row < self.rows and index < len(self.items):
            if index not in self.indices():
                self.select(index)
            self.onMenu(event)

    # --- scroll bar: grab the handle and drag, or click the strip to jump there
    BAR_W = 18

    def showBar(self, active):
        self.canvas.itemconfigure(self.thumb, width=8 if active else 4, fill="#c4c9d6" if active else "#8a90a0")
        self.canvas.configure(cursor="hand2" if active else "")

    def onBarPress(self, event):
        if not self.barGeom:
            return
        top, track, start, length = self.barGeom
        self.barBusy = True
        self.barGrab = event.y - start if start <= event.y <= start + length else length / 2 # off the handle: it jumps to the pointer
        self.onBarDrag(event)

    def onBarDrag(self, event):
        if not self.barBusy or not self.barGeom:
            return
        top, track, start, length = self.barGeom
        fraction = min(max((event.y - self.barGrab - top) / max(track - length, 1), 0), 1)
        self.top = round(fraction * max(len(self.items) - self.rows, 0))
        self.queueDraw()

    def onBarRelease(self, event):
        self.barBusy = False

    # --- drawing
    def place(self, x, y, w, h):
        w, h = int(w), int(h)
        if (x, y, w, h) != self.box:
            self.box = (x, y, w, h)
            self.rows = max((h - 12) // self.ROW, 1)
            self.barPhoto = ImageTk.PhotoImage(Image.new("RGBA", (self.BAR_W, max(h - 24, 1)), (0, 0, 0, 2)))
            self.canvas.itemconfigure(self.barHit, image=self.barPhoto)
            self.photos["back"] = roundedImage(w, h, (8, 10, 16, 80), (255, 255, 255, 46), radius=14)
            self.canvas.itemconfigure(self.back, image=self.photos["back"])
            self.canvas.coords(self.back, x, y)
            while len(self.texts) < self.rows:
                self.highlights.append(self.canvas.create_image(-9999, -9999, anchor="nw", tags=self.tags))
                self.texts.append(self.canvas.create_text(
                    -9999, -9999, anchor="w", font=self.font, fill=TEXT, tags=self.tags))
                self.dividers.append(self.canvas.create_line(
                    -9999, -9999, -9999, -9999, fill="#8a90a0", width=1, tags=self.tags))
        self.queueDraw()

    def queueDraw(self):
        if not self.drawPending:
            self.drawPending = True
            self.canvas.after_idle(self.draw)

    def fit(self, text, width):
        if self.font.measure(text) <= width:
            return text
        while text and self.font.measure(text + "...") > width:
            text = text[:-1]
        return text + "..."

    def draw(self):
        self.drawPending = False
        x, y, w, h = self.box
        if w <= 0:
            return
        try:
            self.paint(x, y, w, h)
        except tk.TclError:
            pass # the window is closing

    def paint(self, x, y, w, h):
        self.top = min(max(self.top, 0), max(len(self.items) - self.rows, 0))
        chosen = set(self.indices())
        key = ("row", w, ACCENT)
        if key not in self.photos:
            self.photos[key] = roundedImage(w - 30, self.ROW - 2, hexToRgb(ACCENT) + (200,), None) # stops short of the scroll bar
            for bar in self.highlights:
                self.canvas.itemconfigure(bar, image="") # they still point at the old picture, and a freed image makes later itemconfigure calls fail
            for old in [k for k in self.photos if isinstance(k, tuple) and k != key]:
                del self.photos[old] # sizes and colours from before
        for k, item in enumerate(self.texts):
            index = self.top + k
            if k < self.rows and index < len(self.items):
                picked = index in chosen
                self.canvas.coords(item, x + 16, y + 6 + k * self.ROW + self.ROW / 2)
                self.canvas.itemconfigure(
                    item, text=self.fit(self.items[index], w - 44), fill=onAccent(ACCENT) if picked else TEXT)
                if picked:
                    self.canvas.itemconfigure(self.highlights[k], image=self.photos[key])
                    self.canvas.coords(self.highlights[k], x + 10, y + 6 + k * self.ROW + 1)
                else:
                    self.canvas.coords(self.highlights[k], -9999, -9999)
                if index in self.breaks and k > 0: # the top row's line would sit on the box's edge
                    lineY = y + 6 + k * self.ROW
                    self.canvas.coords(self.dividers[k], x + 14, lineY, x + w - 30, lineY)
                else:
                    self.canvas.coords(self.dividers[k], -9999, -9999, -9999, -9999)
            else:
                self.canvas.coords(item, -9999, -9999)
                self.canvas.coords(self.highlights[k], -9999, -9999)
                self.canvas.coords(self.dividers[k], -9999, -9999, -9999, -9999)
        if len(self.items) > self.rows:
            track = h - 36 # clear of the rounded corners, round ends included
            length = max(track * self.rows / len(self.items), 24)
            start = y + 18 + (track - length) * self.top / (len(self.items) - self.rows)
            self.canvas.coords(self.thumb, x + w - 11, start, x + w - 11, start + length)
            self.canvas.coords(self.barHit, x + w - 2 - self.BAR_W, y + 12)
            self.canvas.tag_raise(self.thumb) # over the rows and their highlights
            self.barGeom = (y + 18, track, start, length)
        else:
            self.canvas.coords(self.thumb, -9999, -9999, -9999, -9999)
            self.canvas.coords(self.barHit, -9999, -9999)
            self.barGeom = None

class GlassLog:
    """Message box on the canvas: the latest lines, wrapped to fit, over a translucent background"""

    def __init__(self, canvas, group="", size=9, extraTag=""):
        self.canvas = canvas
        self.font = tkfont.Font(family=FONT, size=size)
        self.entries, self.box, self.backPhoto = [], (0, 0, 0, 0), None
        tags = tuple(t for t in (group, extraTag) if t)
        self.back = canvas.create_image(0, 0, anchor="nw", tags=tags)
        self.text = canvas.create_text(0, 0, anchor="nw", font=self.font, fill=MUTED, tags=tags)

    def add(self, text):
        self.entries = (self.entries + [T(text)])[-200:]
        self.render()

    def place(self, x, y, w, h):
        w, h = int(w), int(h)
        if (x, y, w, h) != self.box:
            self.box = (x, y, w, h)
            self.backPhoto = roundedImage(w, h, (8, 10, 16, 80), (255, 255, 255, 46), radius=14)
            self.canvas.itemconfigure(self.back, image=self.backPhoto)
            self.canvas.coords(self.back, x, y)
            self.canvas.coords(self.text, x + 12, y + 8)
        self.render()

    def wrap(self, entry, width):
        lines, current = [], ""
        for word in entry.split():
            trial = (current + " " + word).strip()
            if current and self.font.measure(trial) > width:
                lines.append(current)
                current = word
            else:
                current = trial
        return lines + [current]

    def render(self):
        _, _, w, h = self.box
        if w <= 0:
            return
        rows = max((h - 16) // self.font.metrics("linespace"), 1)
        lines = []
        for entry in reversed(self.entries): # newest first, until the box is full
            lines = self.wrap(entry, w - 28) + lines
            if len(lines) >= rows:
                break
        self.canvas.itemconfigure(self.text, text="\n".join(lines[-rows:]))

class LyricsStrip:
    """A few lines of a song's lyrics, the one being sung in the middle. When the next line comes they slide up to it,
    the new line brightening and the old one dimming, instead of jumping. Three lines show; half a line above and
    below is room for the lines sliding in and out, which fade away there"""
    SLIDE_MS = 320
    FADED = (22, 25, 32) # what a line fades to at the strip's top and bottom edges

    def __init__(self, canvas, tags, size=11, shadow=False):
        self.canvas = canvas
        self.font = tkfont.Font(family=FONT, size=size, weight="bold")
        # shadows (on the Chill tab, over the picture) keep pale lines readable
        self.shadows = [canvas.create_text(-9999, -9999, text="", font=self.font, fill="#000000", tags=tags)
                        for _ in range(5)] if shadow else []
        self.items = [canvas.create_text(-9999, -9999, text="", font=self.font, tags=tags) for _ in range(5)]
        self.faded = self.FADED # (set to the picture's colour where the strip sits over it, on the Chill tab)
        self.lines, self.times = [], []
        self.box = (-9999, -9999, 0, 0)
        self.at = self.goal = 0 # the line in the middle (a fraction of the way to the next while sliding), and where it's going
        self.job = None
        self.texts = {} # line -> its text cut to the strip's width

    def setLines(self, lines):
        self.lines = lines or []
        self.times = [t for t, _ in self.lines] if self.lines and self.lines[0][0] is not None else []
        self.at = self.goal = -1 if self.times else 0 # timed: nothing sung yet, the first line waits underneath
        self.texts = {}
        if self.job:
            self.canvas.after_cancel(self.job)
            self.job = None
        self.draw()

    def place(self, x, y, w, h):
        if (x, y, w, h) != self.box:
            self.box, self.texts = (x, y, w, h), {}
            self.draw()

    def follow(self, seconds):
        """Moves to the line being sung at this point of the song"""
        if not self.times:
            return # untimed lyrics stay at the top
        # looked up a slide's length ahead: the slide then ends, the line in the middle, just as it starts to be sung
        index = bisect.bisect_right(self.times, seconds + self.SLIDE_MS / 1000) - 1 # -1: before the first line
        if index == self.goal:
            return
        self.goal = index
        if self.job:
            self.canvas.after_cancel(self.job)
            self.job = None
        if abs(index - self.at) > 2: # a jump (seeking): straight there
            self.at = index
            self.draw()
            return
        origin, started = self.at, time.perf_counter()

        def step():
            self.job = None
            done = min((time.perf_counter() - started) * 1000 / self.SLIDE_MS, 1.0)
            self.at = origin + (index - origin) * done * done * (3 - 2 * done) # slow at both ends
            self.draw()
            if done < 1:
                self.job = self.canvas.after(16, step)
        step()

    def draw(self):
        x, y, w, h = self.box
        lineH, middle = h / 4, y + h / 2
        base = math.floor(self.at)
        for k, item in enumerate(self.items):
            i = base - 2 + k
            offset = i - self.at
            shadow = self.shadows[k] if self.shadows else None
            if x < -1000 or not 0 <= i < len(self.lines) or abs(offset) >= 1.5:
                self.canvas.coords(item, -9999, -9999)
                if shadow:
                    self.canvas.coords(shadow, -9999, -9999)
                continue
            if i not in self.texts:
                self.texts[i] = fitText(self.font, self.lines[i][1] or "♪", w) # an empty line is a break in the singing
            distance = abs(offset)
            color = blend(TEXT, MUTED, distance) if distance <= 1 else blend(MUTED, self.faded, (distance - 1) * 2)
            ty = middle + offset * lineH
            self.canvas.itemconfigure(item, text=self.texts[i], fill=color)
            self.canvas.coords(item, x + w / 2, ty)
            if shadow:
                self.canvas.itemconfigure(shadow, text=self.texts[i])
                self.canvas.coords(shadow, (x + w / 2 + 1, ty + 1) if distance <= 1 else (-9999, -9999))

class SearchBox:
    """Rounded text box on the canvas with grey placeholder text. onChange() runs whenever the typed text changes"""
    HINT = "Search name, album or artist..."

    def __init__(self, canvas, group, onChange, hint=HINT):
        self.canvas, self.onChange, self.hint = canvas, onChange, T(hint)
        self.hinting, self.photo, self.width = True, None, 0
        self.back = canvas.create_image(0, 0, anchor="nw", tags=(group,))
        self.entry = tk.Entry(
            canvas, font=(FONT, 10), bg="#1b1e26", fg=MUTED, insertbackground=TEXT, relief="flat", borderwidth=0,
            highlightthickness=0, selectbackground=ACCENT, selectforeground=onAccent(ACCENT))
        self.window = canvas.create_window(0, 0, window=self.entry, anchor="w", tags=(group,))
        self.setHint(True)
        self.entry.bind("<FocusIn>", lambda e: self.hinting and self.setHint(False))
        self.entry.bind("<FocusOut>", lambda e: not self.entry.get() and self.setHint(True))
        self.entry.bind("<KeyRelease>", lambda e: self.hinting or self.onChange())
        self.entry.bind("<Escape>", lambda e: (self.clear(), canvas.focus_set()))

    def text(self):
        return "" if self.hinting else self.entry.get().strip()

    def setHint(self, on):
        self.entry.delete(0, "end") # the grey hint is only ever placeholder text, so it goes as soon as you click in
        self.hinting = on
        if on:
            self.entry.insert(0, self.hint)
        self.entry.configure(fg=MUTED if on else TEXT)

    def clear(self):
        self.setHint(self.entry.focus_get() is not self.entry)
        self.onChange()

    def place(self, x, y, width, blurred=None):
        """blurred: the blurred background picture, so the (opaque) native entry can take on the colour showing through the box"""
        if width != self.width:
            self.width = width
            self.photo = roundedImage(width, 30, (0, 0, 0, 70), (255, 255, 255, 50), radius=10) # see-through, like the buttons
            self.canvas.itemconfigure(self.back, image=self.photo)
        color = (20, 23, 29)
        if blurred is not None:
            box = (max(int(x), 0), max(int(y), 0), min(int(x + width), blurred.width), min(int(y + 30), blurred.height))
            if box[2] > box[0] and box[3] > box[1]:
                r, g, b = blurred.crop(box).resize((1, 1), Image.BOX).getpixel((0, 0))
                r, g, b = ((c * 0.6 + d * 0.4) * 0.765 + c * 0.235 for c, d in ((r, 12), (g, 14), (b, 20))) # the frosted panel under it
                color = tuple(int(c * 0.725) for c in (r, g, b)) # and the box's own dark tint
        self.entry.configure(bg="#%02x%02x%02x" % color)
        self.canvas.coords(self.back, x, y)
        self.canvas.coords(self.window, x + 12, y + 15)
        self.canvas.itemconfigure(self.window, width=width - 24, height=20)

class GlassMenu:
    """Right-click menu drawn like the rest of the window: a dark rounded panel with the theme colour as the highlight.
    Entries are dicts: {"label", "command"}, {"label", "sub": [entries]} for a second page, {"label", "disabled": True},
    or None for a divider line. Labels are translated, unless the entry has "translate": False (a playlist's name)"""
    ROW, SEP, PAD, KEY = 30, 9, 6, "#010203" # KEY is the colour the window is made see-through in, to round its corners

    def __init__(self, root):
        self.root, self.win = root, None
        self.font = tkfont.Font(family=FONT, size=10)

    def show(self, x, y, entries):
        self.close()
        self.pos, self.stack, self.hover = (x, y), [entries], None
        win = self.win = tk.Toplevel(self.root)
        win.withdraw()
        win.overrideredirect(True)
        win.attributes("-topmost", True)
        win.configure(bg=self.KEY)
        win.attributes("-transparentcolor", self.KEY)
        self.canvas = canvas = tk.Canvas(win, bg=self.KEY, highlightthickness=0)
        canvas.pack(fill="both", expand=True)
        self.back = canvas.create_image(0, 0, anchor="nw")
        self.bar = canvas.create_image(-9999, -9999, anchor="nw")
        canvas.bind("<Motion>", self.onMotion)
        canvas.bind("<Leave>", lambda e: self.setHover(None))
        canvas.bind("<ButtonPress-1>", self.onClick)
        win.bind("<ButtonPress-1>", lambda e: e.widget is win and self.close()) # a click outside the panel
        win.bind("<Escape>", lambda e: self.close())
        win.bind("<FocusOut>", lambda e: e.widget is win and self.close())
        self.render()
        win.deiconify()
        win.update_idletasks()
        win.focus_force()
        try:
            win.grab_set()
        except tk.TclError:
            pass

    def close(self):
        if self.win:
            win, self.win = self.win, None
            try:
                win.grab_release()
            except tk.TclError:
                pass
            win.destroy()

    def render(self):
        canvas, page = self.canvas, self.stack[-1]
        rows = ([{"label": "‹  Back", "back": True}] if len(self.stack) > 1 else []) + list(page)
        label = lambda row: T(row["label"]) if row.get("translate", True) else row["label"]
        shown = [(label(row) + "     ›" if "sub" in row else label(row)) if row else None for row in rows]
        w = max(max((self.font.measure(t) for t in shown if t), default=0) + 2 * self.PAD + 32, 180)
        h, tops = self.PAD, []
        for row in rows:
            tops.append(h)
            h += self.SEP if row is None else self.ROW
        h += self.PAD
        x, y = self.pos
        x, y = max(min(x, self.root.winfo_screenwidth() - w - 4), 0), max(min(y, self.root.winfo_screenheight() - h - 48), 0)
        self.win.geometry(f"{w}x{h}+{x}+{y}")
        canvas.configure(width=w, height=h)
        canvas.delete("row")
        self.backPhoto = roundedImage(w, h, (22, 25, 32, 255), (255, 255, 255, 56), radius=12)
        self.barPhoto = roundedImage(w - 2 * self.PAD, self.ROW - 2, hexToRgb(ACCENT) + (255,), None, radius=8)
        canvas.itemconfigure(self.back, image=self.backPhoto)
        canvas.itemconfigure(self.bar, image=self.barPhoto)
        canvas.coords(self.bar, -9999, -9999)
        self.rows, self.texts, self.hover = [], [], None
        for row, top in zip(rows, tops):
            if row is None:
                mid = top + self.SEP // 2
                canvas.create_line(self.PAD + 10, mid, w - self.PAD - 10, mid, fill="#3a3f4d", tags="row")
                self.rows.append((top, top + self.SEP, None))
                self.texts.append(None)
                continue
            disabled = row.get("disabled")
            color = MUTED if disabled else TEXT
            text = canvas.create_text(self.PAD + 14, top + self.ROW // 2, anchor="w", text=label(row), fill=color,
                                      font=(FONT, 10), tags="row")
            if "sub" in row:
                canvas.create_text(w - self.PAD - 14, top + self.ROW // 2, anchor="e", text="›", fill=color, font=(FONT, 12, "bold"), tags="row")
            self.rows.append((top, top + self.ROW, None if disabled else row))
            self.texts.append(text)
        canvas.tag_raise("row")

    def rowAt(self, y):
        for index, (top, bottom, _) in enumerate(self.rows):
            if top <= y < bottom:
                return index
        return None

    def onMotion(self, event):
        self.setHover(self.rowAt(event.y))

    def setHover(self, index):
        if index is not None and self.rows[index][2] is None:
            index = None
        if index == self.hover:
            return
        if self.hover is not None and self.texts[self.hover]:
            self.canvas.itemconfigure(self.texts[self.hover], fill=TEXT)
        self.hover = index
        if index is None:
            self.canvas.coords(self.bar, -9999, -9999)
            return
        self.canvas.coords(self.bar, self.PAD, self.rows[index][0] + 1)
        self.canvas.tag_lower(self.bar, "row") # under the text
        self.canvas.itemconfigure(self.texts[index], fill=onAccent(ACCENT))

    def onClick(self, event):
        index = self.rowAt(event.y)
        entry = self.rows[index][2] if index is not None else None
        if entry is None:
            return
        if entry.get("back"):
            self.stack.pop()
            self.render()
        elif "sub" in entry:
            self.stack.append(entry["sub"])
            self.render()
        else:
            self.close()
            self.root.after_idle(entry["command"])

class GlassDialog:
    """Pop-up window in the same frosted-glass style as the main window: blurred picture, pill buttons, rounded fields"""

    def __init__(self, app, title, width, height):
        self.app, self.width, self.height = app, width, height
        self.photos = []
        self.win = win = tk.Toplevel(app.root)
        win.title(T(title))
        win.configure(bg=BG)
        win.transient(app.root)
        win.resizable(False, False)
        x = app.root.winfo_rootx() + (app.root.winfo_width() - width) // 2
        y = app.root.winfo_rooty() + max((app.root.winfo_height() - height) // 3, 20)
        win.geometry(f"{width}x{height}+{x}+{y}")
        self.canvas = tk.Canvas(win, width=width, height=height, highlightthickness=0, bg=BG)
        self.canvas.pack()
        self.backdrop = self.makeBackdrop()
        if self.backdrop:
            self.photos.append(ImageTk.PhotoImage(self.backdrop))
            self.canvas.create_image(0, 0, anchor="nw", image=self.photos[-1])
        card = roundedImage(width - 24, height - 24, (255, 255, 255, 14), (255, 255, 255, 60), radius=22)
        self.photos.append(card)
        self.canvas.create_image(12, 12, anchor="nw", image=card)
        win.bind("<Escape>", lambda e: self.close())
        win.bind("<Destroy>", self.onDestroy)
        app.dialogs.add(win)
        app.tintTitleBars()

    def makeBackdrop(self):
        source = self.app.bgSource
        if not source:
            return None
        iw, ih = source.size
        scale = max(self.width / iw, self.height / ih)
        scaled = source.resize((int(iw * scale) + 1, int(ih * scale) + 1), Image.BILINEAR)
        left, top = (scaled.width - self.width) // 2, (scaled.height - self.height) // 2
        cropped = scaled.crop((left, top, left + self.width, top + self.height))
        small = cropped.resize((max(self.width // 4, 1), max(self.height // 4, 1)), Image.BILINEAR)
        blurred = small.filter(ImageFilter.GaussianBlur(3)).resize((self.width, self.height), Image.BILINEAR)
        return Image.blend(blurred, Image.new("RGB", blurred.size, (12, 14, 20)), 0.55)

    def onDestroy(self, event):
        if event.widget is self.win: # forget this window's buttons so a theme change doesn't repaint dead ones
            GlassButton.instances = [b for b in GlassButton.instances if b.canvas is not self.canvas]

    def close(self):
        self.win.destroy()

    def label(self, text, x, y, size=9, bold=False, color=MUTED, width=0):
        label = GlassLabel(self.canvas, text, size, bold, color)
        label.place(x, y, width)
        return label

    def button(self, text, x, y, width, command, look="normal"):
        button = GlassButton(self.canvas, text, command, look)
        button.place(x, y, width, 36)
        return button

    def field(self, x, y, width):
        """Text box: a rounded translucent outline with a native entry inside, coloured to blend with the picture"""
        box = roundedImage(width, 40, (0, 0, 0, 70), (255, 255, 255, 50), radius=12)
        self.photos.append(box)
        self.canvas.create_image(x, y, anchor="nw", image=box)
        color = "#14171d"
        if self.backdrop:
            r, g, b = self.backdrop.crop((x, y, x + width, y + 40)).resize((1, 1), Image.BOX).getpixel((0, 0))
            color = "#%02x%02x%02x" % (int(r * 0.73), int(g * 0.73), int(b * 0.73)) # the translucent box darkens it a little
        entry = tk.Entry(
            self.canvas, font=(FONT, 11), bg=color, fg=TEXT, insertbackground=TEXT, relief="flat", borderwidth=0,
            highlightthickness=0, selectbackground=ACCENT, selectforeground=onAccent(ACCENT))
        self.canvas.create_window(x + 14, y + 20, window=entry, anchor="w", width=width - 28, height=26)
        return entry

    def onReturn(self, callback):
        self.win.bind("<Return>", callback)

    def show(self, focus=None):
        self.win.update_idletasks()
        self.win.wait_visibility()
        self.win.grab_set()
        if focus:
            focus.focus_set()

# ---- the app -----------------------------------------------------------------------------------------------------
class App:
    """The window: header (title, visualizer, tabs, clock), and the Library, Playlists, Radio and Settings tabs.
    Background threads never touch the window; they put events on self.events, which pump() handles every 100 ms."""
    LIBRARY_HINT = "LIBRARY  ·  drop music files here"
    MIN_SIZE = (760, 600) # tall enough for the Settings page

    def __init__(self, root):
        self.root = root
        root.withdraw() # stay hidden until everything is laid out, so the window never shows its half-built state
        self.events = queue.Queue()
        self.player = Player(lambda state, text: self.events.put(("state", state, text)))
        self.player2 = Player(lambda state, text: self.events.put(("state2", state, text)), channel=2) # the second channel
        self.players = (self.player, self.player2)
        # its own audio process starts a little after the window, so the start-up isn't any slower
        root.after(4000, lambda: threading.Thread(target=self.player2.warmUp, daemon=True).start())
        self.dual = False # the second player is showing (it opens when a song is started on channel two)
        self.dualT = 0.0 # how far the two-player layout has come: 0 one player, 1 two side by side (animated in between)
        self.dualJob = None
        self.compact = False # the first player wears its narrow look: symbol buttons, a smaller name
        self.active2, self.nowTrack2, self.seeking2 = False, None, False
        self.lyrics = {1: None, 2: None} # each channel's song's lyrics, [(seconds, text)], from its .lrc file
        self.lyricClock = {1: (0.0, 0.0), 2: (0.0, 0.0)} # each channel's last reported position, and when it came
        self.lyricsOpen = 0 # the channel whose lyrics fill the library page's player area (0: none)
        self.lyricsLine, self.lyricsScrolled = None, 0.0 # the line marked in that list, and when it was last scrolled by hand
        self.chillLyricsOn = {1: False, 2: False} # the Chill tab's L buttons
        self.playerArea = None # where the library page's players go: x, width, top, height, gap
        # started before the window is even built, so PowerShell's start-up and the engine compile overlap with it
        threading.Thread(target=self.player.warmUp, daemon=True).start()
        threading.Thread(target=listenForMediaKeys, args=(self.events,), daemon=True).start()
        self.stopListening = None # call it to stop the voice thread
        self.voskModel = None # loaded on first use of voice, it takes a second or two
        self.voiceRebuild = False # the library changed: the phrases the recogniser listens for need rebuilding
        self.songs = [] # what the library list shows (the search narrows it)
        self.allSongs = [] # every song, in the chosen order
        self.addedRank = {} # song (normcase path) -> its place in the Added order
        self.seeking = False
        self.stationRequest = 0
        self.voiceOn = False
        self.logUntil = 0.0 # the voice log also shows briefly for voice problems
        self.stations = loadStations()
        self.playlists = loadPlaylists()
        self.libraryPaths = loadLibrary()
        self.tagCache = loadTagCache() # path -> {"m": modified time, "artist", "album", "track"}
        self.libOpen = False # the library panel is expanded over the player
        self.dropping = False
        self.rowWidth = 0 # pixels the longest list row needs
        self.rowWidthCache, self.existsCache = {}, {} # row text -> pixels, song file -> found on disk
        self.libWidthsShown = None # (resting, current) widths the song panel was last drawn at
        self.libGeometry = None # set by the first relayout
        self.laidOutSize = (0, 0) # the window size relayout() last ran for
        self.settings = loadSettings()
        global LANGUAGE
        LANGUAGE = self.settings["language"] = self.settings["language"] or systemLanguage() # before any words are drawn
        setAccent(self.settings["accent"])
        for player in self.players:
            player.setEq(*(self.settings['eq'][b] for b in ('bass', 'mid', 'treble')))
            player.setFades(self.settings["fadeIn"], self.settings["fadeOut"])
        self.lastTab = "library" # the tab the Settings button goes back to
        self.active = False # a track is loaded (playing or paused)
        self.lastPlayPause = 0.0 # when the last play/pause media key was acted on
        self.thumbBar = None # the taskbar preview's buttons, made just before the window is shown
        self.dialogs = set() # the pop-up windows that are open, whose title bars also take the theme colour
        self.bgAverage = BG # the background's average colour, for Title bar from picture
        self.mediaShown = None # (status, title) last shown in Windows' media controls

        root.title("Lettuce Player")
        root.geometry("820x600")
        root.minsize(*self.MIN_SIZE)
        root.configure(bg=BG)
        try:
            root.iconbitmap(default=str(resourcePath(ICON_FILE)))
        except tk.TclError:
            pass # no icon file: keep the default one
        root.protocol("WM_DELETE_WINDOW", self.close)
        self.buildLayout()
        for target in (root, self.canvas):
            target.drop_target_register(DND_FILES)
            target.dnd_bind("<<DropEnter>>", self.onDropEnter)
            target.dnd_bind("<<DropLeave>>", self.onDropLeave)
            target.dnd_bind("<<Drop>>", self.onDrop)
        self.refreshSongs()
        videos = dict.fromkeys(youTubeId(p) for p in self.libraryPaths + [t for pl in self.playlists for t in pl["tracks"]] if isYouTube(p))
        threading.Thread(target=lambda: upgradeYouTubeCovers(videos) and self.events.put(("coversUpgraded",)), daemon=True).start()
        self.tick()
        self.animateVis()
        self.pump()
        root.update_idletasks()
        try:
            self.thumbBar = ThumbBar(root, self.events, {ThumbBar.PREV: self.player.previous, ThumbBar.PLAY: self.toggleAll,
                                            ThumbBar.NEXT: self.player.next})
        except Exception:
            self.thumbBar = None # no preview buttons, everything else works the same
        root.deiconify() # now it can be shown, fully drawn
        self.tintTitleBars()
        root.lift() # and in front of the other windows: Windows won't raise a new window by itself, so it is made topmost for a moment
        root.attributes("-topmost", True)
        root.after(300, lambda: root.attributes("-topmost", self.mini)) # mini mode keeps it
        root.focus_force()

    def buildLayout(self):
        canvas = self.canvas = tk.Canvas(self.root, highlightthickness=0, bg=BG)
        canvas.pack(fill="both", expand=True)
        self.bgItem = canvas.create_image(0, 0, anchor="nw")
        self.nightActive = self.wantNight()
        self.bgPhoto = None
        self.bgCropped = None # the background at the window's size, which the next background fades in from
        self.bgFadeJob, self.bgFadePhoto = None, None
        self.fadeNextBackground = False # the next relayout fades into its new background instead of switching
        self.plainBackground = (None, None) # (what it was loaded from, picture): the day / night picture, kept for songs without a cover
        self.artData = None # the playing song's cover, as picture bytes
        self.bgSource = self.currentBackground()
        self.bgFor = (None, None) # the picture and window size the scaled background was made for
        self.bgAnimation, self.bgAnimationJob = None, None # an animated background's frames as they play
        self.dirtyTabs = set() # tabs that still need laying out for the current window size
        self.tabGeometry = (0, 0)
        self.panelPhotos = {}
        self.resizeJob = None
        lib, rad, cfg, pls = "tab_library", "tab_radio", "tab_settings", "tab_playlists"

        # Glass panels: one image item each, sized in relayout()
        self.panels = {
            "songs": canvas.create_image(0, 0, anchor="nw", tags=("panel", lib)),
            "player": canvas.create_image(0, 0, anchor="nw", tags=("panel", lib)),
            "radio": canvas.create_image(0, 0, anchor="nw", tags=("panel", rad)),
            "chill": canvas.create_image(0, 0, anchor="nw", tags=("panel", "tab_chill")),
            "settings": canvas.create_image(0, 0, anchor="nw", tags=("panel", cfg)),
            "playlists": canvas.create_image(0, 0, anchor="nw", tags=("panel", pls)),
            "tracks": canvas.create_image(0, 0, anchor="nw", tags=("panel", pls)),
            "header": canvas.create_image(0, 0, anchor="nw", tags=("panel",)),
        }

        # Header and tabs, always visible
        self.title = GlassLabel(canvas, "Lettuce Player", 14, True, anchor="w")
        self.clock = GlassLabel(canvas, "", 8, color=TEXT, anchor="e")
        self.titleWidth = tkfont.Font(family=FONT, size=14, weight="bold").measure("Lettuce Player")
        self.visBars = [canvas.create_line(0, 0, 0, 0, width=3, capstyle="butt", fill=ACCENT) for _ in range(VIS_BARS)]
        # channel two's bars: beside the first set in the header, in its own Chill panel, and on its row in mini mode
        self.visBars2 = [canvas.create_line(-9999, 0, -9999, 0, width=3, capstyle="butt", fill=ACCENT) for _ in range(VIS_BARS)]
        self.headerVis2 = self.chillVis2 = self.miniVis2 = self.visBox2 = (0, 0, 24)
        self.visBox = (0, 0, 24) # left edge, baseline, tallest bar: the one of the three below that is showing
        self.headerVis = self.chillVis = self.miniVis = (0, 0, 24) # in the header, in the Chill tab's panel, in mini mode
        self.visQueue = collections.deque(maxlen=120) # (time to show it, levels, channel) waiting for their sound to be heard
        self.visShown, self.visShown2 = [0.0] * VIS_BARS, [0.0] * VIS_BARS # what each set of bars shows now
        self.visTargets = {1: [0.0] * VIS_BARS, 2: [0.0] * VIS_BARS} # each channel's latest levels (the bars show the louder)
        self.visLasts = {1: 0.0, 2: 0.0} # when each channel last reported
        self.visJob = None # the visualizer's next frame, while its loop is running
        self.settingsButton = GlassButton(canvas, "Settings", self.toggleSettings)
        self.tabButtons = {
            "library": GlassButton(canvas, "Library", lambda: self.showTab("library")),
            "playlists": GlassButton(canvas, "Playlists", lambda: self.showTab("playlists")),
            "radio": GlassButton(canvas, "Radio", lambda: self.showTab("radio")),
            "chill": GlassButton(canvas, "Chill", lambda: self.showTab("chill")),
        }
        self.miniButton = GlassButton(canvas, "Mini mode", self.toggleMini)
        self.mini = False # the small window with just the song name and the main controls
        self.normalSize = "820x600" # the window's geometry before mini mode, to come back to
        self.wasMaximized = False # the window was maximized before mini mode, and is maximized again after it
        self.fullscreen = False # F11: the window fills the screen, with a small box in the corner to shrink it back
        self.chillFullscreen = False # the Chill tab made it full screen, so leaving the tab shrinks it again
        self.shrinkButton = GlassButton(canvas, "\ue73f", self.toggleFullscreen, size=11, family="Segoe MDL2 Assets") # "back to window"
        for item in (self.panels["header"], self.title.item, self.clock.item, self.settingsButton.image, self.settingsButton.caption,
                     self.miniButton.image, self.miniButton.caption, self.shrinkButton.image, self.shrinkButton.caption,
                     *(i for b in self.tabButtons.values() for i in (b.image, b.caption))):
            canvas.addtag_withtag("full_header", item) # everything in the header that mini mode hides

        # Library tab: song list
        self.veil = canvas.create_image(-9999, -9999, anchor="nw", tags=(lib,)) # blurs the player while the library is open
        self.veilPhoto = None
        canvas.tag_bind(self.veil, "<ButtonPress-1>", lambda e: self.libOpen and self.toggleLibrary()) # a click off the open library closes it
        self.libraryLabel = GlassLabel(canvas, self.LIBRARY_HINT, 9, color=MUTED, group=lib)
        self.sortButtons = {}
        for mode, text in LIST_SORT_MODES:
            self.sortButtons[mode] = GlassButton(canvas, text, lambda m=mode: self.setSort(m), group=lib, size=9)
        self.search = SearchBox(canvas, lib, self.onSearchChange)
        self.arrowButton = GlassButton(canvas, "→", self.toggleLibrary, "accent", group=lib, size=11)
        self.youtubeButton = GlassButton(canvas, "+YT", self.addYouTubeDialog, group=lib, size=9) # only while YouTube is on
        self.listbox = GlassList(canvas, lib, 10, onActivate=self.playSelected, onDelete=self.removeSelectedSong,
                                 onMenu=self.showSongMenu, onSelect=self.updateLibraryLabel, multi=True,
                                 onActivate2=self.playSelected2)
        self.songMenu = GlassMenu(self.root)

        # Library tab: now playing and controls
        self.nowPlaying = GlassLabel(canvas, T("Nothing playing"), 18, True, group=lib, translate=False)
        self.titleFont = tkfont.Font(family=FONT, size=18, weight="bold") # the same font, to count the song name's lines
        self.titleText = T("Nothing playing") # the whole name (what's drawn may be cut short)
        self.titleZone = (0, 0) # the song name sits between these two heights: the box's top and the progress bar's top
        self.elapsed = GlassLabel(canvas, "0:00", 9, color=MUTED, anchor="w", group=lib)
        self.total = GlassLabel(canvas, "0:00", 9, color=MUTED, anchor="e", group=lib)
        self.seekBar = GlassSlider(
            canvas, onPress=lambda: setattr(self, "seeking", True), onRelease=self.onSeekRelease, group=lib)
        self.prevButton = GlassButton(canvas, "Prev", self.player.previous, group=lib)
        self.playButton = GlassButton(canvas, "Play", self.onPlayButton, "accent", group=lib)
        self.nextButton = GlassButton(canvas, "Next", self.player.next, group=lib)
        self.muteButton = GlassButton(canvas, "Mute", self.toggleMute, group=lib, size=9)
        self.shuffleButton = GlassButton(canvas, "Shuffle: Off", self.toggleShuffle, group=lib, size=9)
        self.player.shuffle = self.settings["shuffle"]
        self.loopButton = GlassButton(canvas, LOOP_MODES[self.settings["loop"]], self.cycleLoop, group=lib, size=9)
        self.player.loop = self.settings["loop"]
        self.showLoop()
        self.showShuffle()
        self.volumeLabel = GlassLabel(canvas, "Volume", 9, color=MUTED, anchor="w", group=lib)
        self.volume = GlassSlider(canvas, 0, 1000, command=lambda v: self.setVolume(1, v), group=lib)
        self.volume.set(self.player.volume)
        self.voiceAvailable = voiceInstalled() # without it, the voice row isn't shown at all
        self.voiceLabel = GlassLabel(canvas, "VOICE", 9, color=MUTED, anchor="w", group=lib)
        self.voiceButton = GlassButton(canvas, "Voice: Off", self.toggleVoice, group=lib)
        self.voiceInfoButton = GlassButton(canvas, "i", self.showVoiceHelp, group=lib, size=11) # what can be said, while voice is on
        self.voiceInfoSpot = None # where it goes (x, y), next to the voice button
        self.log = GlassLog(canvas, lib, extraTag="voicelog")

        # Library tab: the second player. It opens to the right of the first when a song is started on channel two
        # (middle-click, or Shift+Enter), and its ✕ closes it again. "deck2" tags its controls, which only show once
        # the panels have finished moving
        self.panels["player2"] = canvas.create_image(-9999, -9999, anchor="nw", tags=("panel", lib))
        self.panels["voice"] = canvas.create_image(-9999, -9999, anchor="nw", tags=("panel", lib)) # the voice row's own panel, under both players
        self.title2 = GlassLabel(canvas, T("Nothing playing"), 13, True, group=lib, translate=False)
        self.title2Font = tkfont.Font(family=FONT, size=13, weight="bold")
        self.title2Text = T("Nothing playing")
        self.art2Item = canvas.create_image(-9999, -9999, anchor="nw", tags=(lib,))
        self.art2Photos, self.art2Path = None, None # (narrow, small) covers of channel two's song
        self.elapsed2 = GlassLabel(canvas, "0:00", 9, color=MUTED, anchor="w", group=lib)
        self.total2 = GlassLabel(canvas, "", 9, color=MUTED, anchor="e", group=lib)
        self.seekBar2 = GlassSlider(canvas, onPress=lambda: setattr(self, "seeking2", True), onRelease=self.onSeekRelease2, group=lib)
        self.prevButton2 = GlassButton(canvas, "⏴⏴", self.player2.previous, group=lib, size=12, family=SYMBOL_FONT)
        self.playButton2 = GlassButton(canvas, "⏵", self.onPlayButton2, "accent", group=lib, size=12, family=SYMBOL_FONT)
        self.nextButton2 = GlassButton(canvas, "⏵⏵", self.player2.next, group=lib, size=12, family=SYMBOL_FONT)
        self.player2.shuffle, self.player2.loop = self.settings["shuffle"], self.settings["loop"] # it starts as the first is set
        self.shuffleButton2 = GlassButton(canvas, "Shuffle", self.toggleShuffle2, group=lib, size=9)
        self.muteButton2 = GlassButton(canvas, "Mute", self.toggleMute2, group=lib, size=9)
        self.loopButton2 = GlassButton(canvas, "Loop", self.cycleLoop2, group=lib, size=9)
        self.volumeLabel2 = GlassLabel(canvas, "Volume", 9, color=MUTED, anchor="w", group=lib)
        self.volume2 = GlassSlider(canvas, 0, 1000, command=lambda v: self.setVolume(2, v), group=lib)
        self.volume2.set(self.player2.volume)
        self.closeButton2 = GlassButton(canvas, "✕", self.closeDual, group=lib, size=10, family=SYMBOL_FONT)
        self.tagAll("deck2", self.title2, self.art2Item, self.elapsed2, self.total2, self.seekBar2, self.prevButton2,
                    self.playButton2, self.nextButton2, self.shuffleButton2, self.muteButton2, self.loopButton2,
                    self.volumeLabel2, self.volume2, self.closeButton2)
        self.player2Box = (0, 0, 0) # x, top and width of the second player's panel
        # lyrics under each player (when its song has an .lrc file), and ⤢ to read them all
        self.libLyrics = {1: LyricsStrip(canvas, (lib,)), 2: LyricsStrip(canvas, (lib, "deck2"))}
        self.lyricsButtons = {channel: GlassButton(canvas, "⤢", lambda c=channel: self.openLyrics(c), group=lib, size=10,
                                                   family=SYMBOL_FONT) for channel in (1, 2)}
        self.tagAll("deck2", self.lyricsButtons[2])
        # all of a song's lyrics, over the player area: scroll through them, double-click a line to go to it
        self.lyricsPanel = canvas.create_image(-9999, -9999, anchor="nw", tags=("lyricsview",))
        self.lyricsPhoto = None
        self.lyricsTitle = GlassLabel(canvas, "", 9, color=MUTED, anchor="w", group="lyricsview")
        self.lyricsClose = GlassButton(canvas, "✕", self.closeLyrics, group="lyricsview", size=10, family=SYMBOL_FONT)
        self.lyricsList = GlassList(canvas, "lyricsview", 11, onActivate=self.seekToLyric)
        self.showShuffle2()
        self.showLoop2()

        # Mini mode: symbols instead of words, so it fits in a small window
        mini = "tab_mini"
        self.panels["mini"] = canvas.create_image(0, 0, anchor="nw", tags=("panel", mini))
        self.miniTitle = GlassLabel(canvas, T("Nothing playing"), 11, True, group=mini, translate=False)
        self.miniFont = tkfont.Font(family=FONT, size=11, weight="bold")
        self.miniButtons = {
            "prev": GlassButton(canvas, "⏴⏴", self.player.previous, group=mini, size=14, family=SYMBOL_FONT),
            "play": GlassButton(canvas, "⏵", self.onPlayButton, "accent", group=mini, size=14, family=SYMBOL_FONT),
            "next": GlassButton(canvas, "⏵⏵", self.player.next, group=mini, size=14, family=SYMBOL_FONT),
            # the speaker is an emoji no font draws quickly (a third of a second), so it is only given its symbol
            # when mini mode is first opened, not at start-up
            "mute": GlassButton(canvas, "", self.toggleMute, group=mini, size=12, family=SYMBOL_FONT),
        }
        self.miniExit = GlassButton(canvas, "⤢", self.toggleMini, group=mini, size=11, family=SYMBOL_FONT)
        # mini mode's second row, for channel two: the window grows downward to fit it
        self.mini2Line = canvas.create_line(0, 0, 0, 0, fill="#3a4050", tags=(mini,))
        self.mini2Title = GlassLabel(canvas, T("Nothing playing"), 11, True, group=mini, translate=False)
        self.mini2ArtItem = canvas.create_image(-9999, -9999, anchor="nw", tags=(mini,))
        self.mini2Buttons = {
            "prev": GlassButton(canvas, "⏴⏴", self.player2.previous, group=mini, size=14, family=SYMBOL_FONT),
            "play": GlassButton(canvas, "⏵", self.onPlayButton2, "accent", group=mini, size=14, family=SYMBOL_FONT),
            "next": GlassButton(canvas, "⏵⏵", self.player2.next, group=mini, size=14, family=SYMBOL_FONT),
            "mute": GlassButton(canvas, "", self.toggleMute2, group=mini, size=12, family=SYMBOL_FONT),
        }
        # each row's volume bar, between its buttons and its visualizer
        self.miniVolumes = {channel: GlassSlider(canvas, 0, 1000, command=lambda v, c=channel: self.setVolume(c, v), group=mini)
                            for channel in (1, 2)}
        for channel, slider in self.miniVolumes.items():
            slider.set(self.players[channel - 1].volume)
        self.tagAll("mini2", self.mini2Line, self.mini2Title, self.mini2ArtItem, *self.mini2Buttons.values(), self.miniVolumes[2])
        self.mini2TextWidth, self.mini2Shown = 0, None
        self.artItem = canvas.create_image(-9999, -9999, anchor="nw", tags=(lib,)) # the cover, above the progress bar
        self.miniArtItem = canvas.create_image(-9999, -9999, anchor="nw", tags=(mini,))
        self.artPhotos = None # (big, small) pictures of the cover of the song playing, None when it has none
        self.artPath = None
        self.titleFadeJob = None
        self.nowBox = (0, 0, 0) # where the song name goes (x, y, width) when there is no cover
        self.miniSize = self.MINI_SIZE
        self.miniTextWidth = 0

        # Chill tab: as little as possible. The song, the progress line and three symbol buttons, in a small panel low down
        chill = "tab_chill"
        self.chillShadow = GlassLabel(canvas, T("Nothing playing"), 13, True, color="#000000", group=chill, translate=False) # keeps the name readable on a pale picture
        self.chillTitle = GlassLabel(canvas, T("Nothing playing"), 13, True, group=chill, translate=False)
        self.chillFont = tkfont.Font(family=FONT, size=13, weight="bold")
        self.chillArtItem = canvas.create_image(-9999, -9999, anchor="nw", tags=(chill,))
        self.chillSeek = GlassSlider(canvas, onPress=lambda: setattr(self, "seeking", True),
                                     onRelease=lambda: self.onSeekRelease(self.chillSeek), group=chill)
        self.chillButtons = {
            "prev": GlassButton(canvas, "⏴⏴", self.player.previous, group=chill, size=14, family=SYMBOL_FONT),
            "play": GlassButton(canvas, "⏵", self.onPlayButton, "accent", group=chill, size=14, family=SYMBOL_FONT),
            "next": GlassButton(canvas, "⏵⏵", self.player.next, group=chill, size=14, family=SYMBOL_FONT),
        }
        self.chillBox = (0, 0, 0, 0) # x, y, width, height of the panel
        # and the second player's panel, to the right of the first while channel two is in use (no close button here)
        self.panels["chill2"] = canvas.create_image(-9999, -9999, anchor="nw", tags=("panel", chill))
        self.chill2Shadow = GlassLabel(canvas, T("Nothing playing"), 13, True, color="#000000", group=chill, translate=False)
        self.chill2Title = GlassLabel(canvas, T("Nothing playing"), 13, True, group=chill, translate=False)
        self.chill2ArtItem = canvas.create_image(-9999, -9999, anchor="nw", tags=(chill,))
        self.chill2Seek = GlassSlider(canvas, onPress=lambda: setattr(self, "seeking2", True),
                                      onRelease=lambda: self.onSeekRelease2(self.chill2Seek), group=chill)
        self.chill2Buttons = {
            "prev": GlassButton(canvas, "⏴⏴", self.player2.previous, group=chill, size=14, family=SYMBOL_FONT),
            "play": GlassButton(canvas, "⏵", self.onPlayButton2, "accent", group=chill, size=14, family=SYMBOL_FONT),
            "next": GlassButton(canvas, "⏵⏵", self.player2.next, group=chill, size=14, family=SYMBOL_FONT),
        }
        self.tagAll("chill2", self.panels["chill2"], self.chill2Shadow, self.chill2Title, self.chill2ArtItem, self.chill2Seek,
                    *self.chill2Buttons.values())
        self.chillBox2 = (0, 0, 0, 0)
        # the L buttons: each player's lyrics, playing above its Chill panel
        self.chillLyricsButtons = {channel: GlassButton(canvas, "L", lambda c=channel: self.toggleChillLyrics(c), group=chill,
                                                        size=10) for channel in (1, 2)}
        self.chillStrips = {1: LyricsStrip(canvas, (chill,), 14), 2: LyricsStrip(canvas, (chill, "chill2"), 14)}
        self.tagAll("chill2", self.chillLyricsButtons[2])
        # each Chill player's volume, at the bottom right of its panel
        self.chillVolumes = {channel: GlassSlider(canvas, 0, 1000, command=lambda v, c=channel: self.setVolume(c, v), group=chill)
                             for channel in (1, 2)}
        for channel, slider in self.chillVolumes.items():
            slider.set(self.players[channel - 1].volume)
        self.tagAll("chill2", self.chillVolumes[2])
        self.chill2TextWidth, self.chill2Shown = 0, None
        self.chillTextWidth = 0
        self.chillShown = None
        self.nowTrack = None # (name, path) of the song playing, for the weather
        self.forcedWeather = set() # "snow" / "rain" asked for by voice, until "stop"
        self.weatherOn = set() # what is falling now
        self.weatherJob, self.weatherTick, self.particles = None, 0, {} # particles: kind -> [flake or drop, ...]
        self.weatherWin = self.weatherCanvas = self.weatherGeometry = None
        self.weatherHidden = False
        self.miniShown = None # what the mini controls last showed, so they only repaint when something changed

        # arrow keys: the control they have chosen gets a white ring around it
        self.navTarget = None
        self.navRing = canvas.create_image(-9999, -9999, anchor="nw")
        self.navRingPhoto, self.navRingKey, self.navRingAt = None, None, None
        # the Chill tab: the header fades away while the mouse is still. During a fade a picture of it stands in for it
        self.headerAlpha = self.headerTarget = 1.0 # how much of the header shows, and where the fade is heading
        self.headerFadeItem = canvas.create_image(-9999, -9999, anchor="nw", state="hidden")
        self.headerFadePhoto = self.headerShot = None
        self.headerFadeJob = self.headerIdleJob = None
        self.lastActivity, self.lastPointer = time.time(), None

        self.root.bind_all("<space>", self.onSpace) # play / pause, except while typing

        # Playlists tab: your playlists on the left, the songs of the selected one on the right
        self.playlistsLabel = GlassLabel(canvas, "PLAYLISTS", 9, color=MUTED, anchor="w", group=pls)
        self.playlistAdd = GlassButton(canvas, "+", self.addPlaylistDialog, "accent", group=pls, size=16)
        self.playlistSearch = SearchBox(canvas, pls, self.onPlaylistSearch, hint="Search playlists...")
        self.playlistShown = [] # the index in self.playlists of each row the list shows (the search narrows it)
        self.playlistList = GlassList(
            canvas, pls, 11, onActivate=self.playSelectedPlaylist, onDelete=self.askDeletePlaylist,
            onSelect=self.onPlaylistSelect, onMove=self.onPlaylistMoved, onMoved=self.persistPlaylists,
            onMenu=self.showPlaylistMenu)
        self.playlistMenu = GlassMenu(self.root)
        self.tracksLabel = GlassLabel(canvas, "SONGS", 9, color=MUTED, anchor="w", group=pls)
        self.addSongsButton = GlassButton(canvas, "Add songs...", self.addSongsToPlaylist, group=pls)
        self.trackSearch = SearchBox(canvas, pls, self.refreshPlaylistTracks)
        self.playlistYouTubeButton = GlassButton(canvas, "+YT", self.addYouTubeToPlaylist, group=pls, size=9) # only while YouTube is on
        self.playlistSortButtons = {}
        for mode, text in LIST_SORT_MODES:
            self.playlistSortButtons[mode] = GlassButton(canvas, text, lambda m=mode: self.setPlaylistSort(m), group=pls, size=9)
        self.trackList = GlassList(
            canvas, pls, 10, onActivate=self.playSelectedTrack, onDelete=self.removeSelectedTrack,
            onSelect=self.onTrackSelect, onMenu=self.showTrackMenu, multi=True, # Ctrl / Shift-click pick several, like the library
            onActivate2=self.playSelectedTrack2)
        self.trackMenu = GlassMenu(self.root)
        self.playlistsListUsed = self.playlistList # which of the two lists the Delete key acts on: the one used last
        self.trackCountShown = False # the status line shows "N songs selected"
        self.playlistStatus = GlassLabel(canvas, "", 10, color=MUTED, group=pls)
        self.refreshPlaylists()

        # Radio tab
        self.stationsLabel = GlassLabel(
            canvas, "STATIONS  ·  double-click to play, drag to reorder", 9, color=MUTED, anchor="w", group=rad)
        self.addButton = GlassButton(canvas, "+", self.addStationDialog, "accent", group=rad, size=16)
        self.removeButton = GlassButton(canvas, "Remove", self.removeStation, group=rad)
        self.stationList = GlassList(
            canvas, rad, 11, onActivate=self.playSelectedStation, onDelete=self.removeStation,
            onMove=self.onStationMoved, onMoved=self.persistStations, handCursor=True, onActivate2=self.playSelectedStation2)
        self.radioStatus = GlassLabel(canvas, "", 10, color=MUTED, group=rad)
        self.refreshStations()

        # Settings view: background picture, theme colour, equalizer and fades
        self.settingsHeader = GlassLabel(canvas, "BACKGROUND  ·  with Night ticked, the night picture is used from 9 PM until 7 AM", 9, color=MUTED, group=cfg)
        self.dayLabel = GlassLabel(canvas, "Day", 10, anchor="w", group=cfg)
        self.bgName = GlassLabel(canvas, "", 10, anchor="w", group=cfg)
        self.chooseButton = GlassButton(canvas, "Choose picture...", self.chooseBackground, "accent", group=cfg)
        self.defaultBgButton = GlassButton(canvas, "Use default", self.resetBackground, group=cfg)
        self.nightCheck = GlassCheck(canvas, "Night", self.toggleNight, group=cfg) # 9 PM to 7 AM
        self.nightCheck.set(self.settings["nightMode"])
        self.funCheck = GlassCheck(canvas, "Fun", self.toggleFun, group=cfg)
        self.funCheck.set(self.settings["fun"])
        self.funText = GlassLabel(canvas, 'Say "snow" or "rain"; snow and rain also fall for songs about them', 10,
                                  color=MUTED, anchor="w", group=cfg)
        self.youtubeCheck = GlassCheck(canvas, "YouTube", self.toggleYouTube, group=cfg)
        self.youtubeCheck.set(self.settings["youtube"])
        self.coverCheck = GlassCheck(canvas, "Cover", self.toggleCover, group=cfg)
        self.coverCheck.set(self.settings["cover"])
        browser = findChromium()
        self.youtubeText = GlassLabel(canvas, f"+YT in the library adds a song; it plays in {Path(browser).stem.capitalize()}" if browser
                                      else "YouTube songs need Google Chrome or Microsoft Edge", 10, color=MUTED, anchor="w", group=cfg)
        self.nightName = GlassLabel(canvas, "", 10, anchor="w", group=cfg)
        self.nightChooseButton = GlassButton(canvas, "Choose picture...", lambda: self.chooseBackground(night=True), "accent", group=cfg)
        self.nightDefaultButton = GlassButton(canvas, "Use default", lambda: self.resetBackground(night=True), group=cfg)
        self.themeHeader = GlassLabel(canvas, "THEME COLOR  ·  buttons, progress and volume lines, list selection", 9, color=MUTED, group=cfg)
        self.swatches = []
        for color in THEME_COLORS:
            item = canvas.create_oval(0, 0, 0, 0, fill=color, outline="#59607a", width=1, tags=(cfg, "swatch"))
            canvas.tag_bind(item, "<ButtonRelease-1>", lambda e, c=color: self.applyTheme(c))
            canvas.tag_bind(item, "<Enter>", lambda e: canvas.configure(cursor="hand2"))
            canvas.tag_bind(item, "<Leave>", lambda e: canvas.configure(cursor=""))
            self.swatches.append((color, item))
        self.swatchRing = canvas.create_oval(0, 0, 0, 0, fill="", outline="#ffffff", width=2, tags=(cfg,)) # marks the chosen colour
        self.customColor = GlassButton(canvas, "Custom...", self.chooseCustomColor, group=cfg)
        self.pictureTitleBarCheck = GlassCheck(canvas, "Title bar from picture", self.togglePictureTitleBar, group=cfg)
        self.pictureTitleBarCheck.set(self.settings["pictureTitleBar"])
        self.coverText = GlassLabel(canvas, "The playing song's cover is the background (the Day picture when it has none)", 10,
                                    color=MUTED, anchor="w", group=cfg)
        self.titleBarText = GlassLabel(canvas, "The window's title bar takes the background's colour, not the theme colour", 10,
                                       color=MUTED, anchor="w", group=cfg)
        self.extrasHeader = GlassLabel(canvas, "EXTRAS", 9, color=MUTED, group=cfg)
        self.languageLabel = GlassLabel(canvas, "Language", 10, anchor="w", group=cfg)
        self.languageButton = GlassButton(canvas, LANGUAGES[LANGUAGE] + "  ▾", self.showLanguageMenu, group=cfg)
        self.languageText = GlassLabel(canvas, "Lettuce Player restarts in the language you pick", 10, color=MUTED, anchor="w", group=cfg)
        self.languageMenu = GlassMenu(self.root)
        # the page scrolls when the window is too short for it: a thin bar at the panel's right edge
        self.settingsScroll = 0 # how far down the page is scrolled, in pixels
        self.settingsBands, self.settingsView, self.settingsMaxScroll = [], (0, 0), 0
        self.settingsTrack = canvas.create_line(0, 0, 0, 0, width=4, capstyle="round", fill="#566074", tags=(cfg, "settingsbar"))
        self.settingsThumb = canvas.create_line(0, 0, 0, 0, width=6, capstyle="round", fill=ACCENT, tags=(cfg, "settingsbar"))
        canvas.tag_bind(self.settingsTrack, "<ButtonPress-1>", self.onSettingsTrack)
        canvas.tag_bind(self.settingsThumb, "<ButtonPress-1>", self.onSettingsThumbDown)
        canvas.tag_bind(self.settingsThumb, "<B1-Motion>", self.onSettingsThumbDrag)
        for item in (self.settingsTrack, self.settingsThumb):
            canvas.tag_bind(item, "<Enter>", lambda e: canvas.configure(cursor="hand2"))
            canvas.tag_bind(item, "<Leave>", lambda e: canvas.configure(cursor=""))
        self.eqHeader = GlassLabel(canvas, "EQUALIZER  ·  changes apply to the music right away", 9, color=MUTED, group=cfg)
        self.eqRows = {}
        for band in ("bass", "mid", "treble"):
            label = GlassLabel(canvas, band.capitalize(), 10, anchor="w", group=cfg)
            slider = GlassSlider(canvas, -12, 12, command=lambda v, b=band: self.onEq(b, v), onRelease=self.saveEq, group=cfg)
            slider.set(self.settings["eq"][band])
            readout = GlassLabel(canvas, self.eqText(self.settings["eq"][band]), 10, anchor="e", group=cfg)
            self.eqRows[band] = (label, slider, readout)
        self.fadeHeader = GlassLabel(canvas, "FADES  ·  how long songs take to fade in and out", 9, color=MUTED, group=cfg)
        self.fadeRows = {}
        for key, text in (("fadeIn", "Fade in"), ("fadeOut", "Fade out")):
            label = GlassLabel(canvas, text, 10, anchor="w", group=cfg)
            slider = GlassSlider(canvas, 0, 10, command=lambda v, k=key: self.onFade(k, v), onRelease=self.saveEq, group=cfg)
            slider.set(self.settings[key])
            readout = GlassLabel(canvas, self.fadeText(self.settings[key]), 10, anchor="e", group=cfg)
            self.fadeRows[key] = (label, slider, readout)
        self.eqReset = GlassButton(canvas, "Reset", self.resetEq, group=cfg)
        self.fadeReset = GlassButton(canvas, "Reset", self.resetFades, group=cfg)
        self.settingsStatus = GlassLabel(canvas, "", 10, color=MUTED, group=cfg)
        self.showBackgroundName()
        self.markSwatch()

        canvas.bind("<Configure>", self.onResize)
        canvas.bind("<MouseWheel>", self.onWheel)
        for key, dx, dy in (("Left", -1, 0), ("Right", 1, 0), ("Up", 0, -1), ("Down", 0, 1)):
            self.root.bind_all(f"<{key}>", lambda e, dx=dx, dy=dy: self.onArrow(e, dx, dy))
        self.root.bind_all("<Return>", self.onReturn)
        self.root.bind_all("<Escape>", self.onEscape)
        self.root.bind_all("<F11>", lambda e: self.keysAreOurs(e) and not self.mini and self.toggleFullscreen())
        canvas.bind("<Motion>", self.onPointerMove, add="+")
        canvas.bind("<ButtonPress>", self.onPointerPress, add="+")
        canvas.bind("<Control-a>", self.onSelectAll)
        canvas.bind("<Delete>", lambda e: self.onDeleteKey())
        self.showSortButtons()
        self.showTab("library")
        self.root.update_idletasks()
        w, h = canvas.winfo_width(), canvas.winfo_height()
        if w < 200: # the window is still hidden, so the canvas has no size yet: it will fill the window
            w, h = self.root.winfo_width(), self.root.winfo_height()
        self.relayout(w, h)

    def showTab(self, name):
        if name == "chill" and self.currentTab != "chill" and not self.fullscreen:
            self.setFullscreen(True) # the Chill tab is for looking at: it takes the whole screen
            self.chillFullscreen = True
        elif name != "chill" and self.chillFullscreen:
            self.setFullscreen(False)
        self.currentTab = name
        if name not in ("settings", "mini"):
            self.lastTab = name
        self.resetHeader() # whole again, and on the Chill tab its 3 seconds start
        self.layoutTab(name) # a tab is only laid out once it is shown
        self.applyTabVisibility()
        self.updateVisBox()
        self.chillShown = None
        self.syncChill()
        self.resumeBackground()
        for tab, button in self.tabButtons.items():
            button.configure(style="Accent.TButton" if tab == name else "TButton")
        self.settingsButton.configure(style="Accent.TButton" if name == "settings" else "TButton")

    def applyTabVisibility(self):
        """Shows the current tab's items and hides the rest. Also run after every relayout: list rows are created lazily
        and would otherwise start out visible"""
        for tab in ("library", "playlists", "radio", "chill", "settings", "mini"):
            self.canvas.itemconfigure(f"tab_{tab}", state="normal" if tab == self.currentTab else "hidden")
        self.canvas.itemconfigure("full_header", state="hidden" if self.mini or self.headerAlpha < 1 else "normal")
        if not (self.dual and self.dualT >= 1): # the second player's controls wait until its panel has fully opened
            self.canvas.itemconfigure("deck2", state="hidden")
        if not self.dual:
            self.canvas.itemconfigure("chill2", state="hidden")
            self.canvas.itemconfigure("mini2", state="hidden")
        self.canvas.itemconfigure("lyricsview", state="normal" if self.lyricsOpen and self.currentTab == "library"
                                  and not self.mini else "hidden")
        if self.currentTab == "settings" and not self.mini:
            self.clipSettings()
        self.refreshLogVisibility()
        if self.navTarget is not None:
            self.placeNavRing() # its control may have just gone out of sight

    def refreshLogVisibility(self):
        visible = self.currentTab == "library" and (self.voiceOn or time.time() < self.logUntil)
        self.canvas.itemconfigure("voicelog", state="normal" if visible else "hidden")

    def showLogFor(self, seconds):
        """Voice problems need to be seen even while voice is off"""
        self.logUntil = time.time() + seconds
        self.refreshLogVisibility()
        self.root.after(int(seconds * 1000) + 100, self.refreshLogVisibility)

    def activeList(self):
        if self.lyricsOpen and self.currentTab == "library":
            return self.lyricsList
        return {"library": self.listbox, "playlists": self.playlistList, "radio": self.stationList}.get(self.currentTab)

    def onDeleteKey(self):
        """Delete acts on the tab's list; on the Playlists tab, on the songs when they were what was picked last"""
        target = self.playlistsListUsed if self.currentTab == "playlists" else self.activeList()
        if target and target.onDelete:
            target.onDelete()

    def onWheel(self, event):
        if self.currentTab == "settings" and not self.mini and self.libGeometry:
            box = self.canvas.bbox(self.panels["settings"])
            if box and box[0] <= event.x <= box[2] and box[1] <= event.y <= box[3]:
                self.scrollSettings(-self.SCROLL_STEP if event.delta > 0 else self.SCROLL_STEP)
                return
        for lst in GlassList.instances:
            if lst.contains(event.x, event.y) and self.canvas.itemcget(lst.back, "state") != "hidden":
                lst.scroll(-3 if event.delta > 0 else 3)
                if lst is self.lyricsList:
                    self.lyricsScrolled = time.time() # it stops following the song for a few seconds
                return

    def toggleSettings(self):
        self.showTab(self.lastTab if self.currentTab == "settings" else "settings")

    # ---- arrow keys: they move between the controls on screen, and a white ring shows the one chosen -------------
    # Up / Down move through a list's rows (and leave it at either end), Left / Right move a slider, Enter presses
    # what is chosen, Escape or a click hides the ring
    def navControls(self):
        """Every control the arrow keys can reach right now, with its box: [(control, (x0, y0, x1, y1))]"""
        everything = (*GlassButton.instances, *GlassCheck.instances, *GlassSlider.instances, *GlassList.instances,
                      self.search, self.trackSearch, *self.swatches)
        return [(control, rect) for control in everything for rect in (self.navRect(control),) if rect]

    def navRect(self, control):
        """The control's box on the canvas, or None while it is hidden, off screen, or under the open library's veil"""
        canvas = self.canvas
        if isinstance(control, tuple): # a theme colour: (colour, its circle)
            item = control[1]
            rect = canvas.coords(item)
        elif control.canvas is not canvas:
            return None # part of a dialog
        elif isinstance(control, GlassButton):
            item = control.image
            x, y = canvas.coords(item)
            rect = (x, y, x + control.size[0], y + control.size[1])
        elif isinstance(control, GlassCheck):
            item = control.box
            x, y = canvas.coords(item)
            rect = (x, y, (canvas.bbox(control.label.item) or (0, 0, x + 22))[2], y + 22)
        elif isinstance(control, SearchBox):
            item = control.back
            x, y = canvas.coords(item)
            rect = (x, y, x + control.width, y + 30)
        else: # a slider or a list
            item = control.hit if isinstance(control, GlassSlider) else control.back
            x, y, w, h = control.box
            rect = (x, y, x + w, y + h)
        if len(rect) < 4 or rect[0] < -1000 or rect[2] - rect[0] < 2:
            return None
        tags = canvas.gettags(item)
        if "full_header" in tags:
            if self.mini:
                return None # (a faded header still counts: the arrow key that reaches it brings it back)
        elif canvas.itemcget(item, "state") == "hidden":
            return None
        if self.libOpen and self.currentTab == "library" and "tab_library" in tags: # the player is veiled
            songs = canvas.bbox(self.panels["songs"])
            if songs and rect[2] > songs[2]:
                return None
        return tuple(rect)

    def keysAreOurs(self, event):
        """Keys pressed in the main window, not in a dialog or a menu"""
        try:
            return event.widget.winfo_toplevel() is self.root
        except (AttributeError, tk.TclError):
            return False

    def onArrow(self, event, dx, dy):
        if not self.keysAreOurs(event):
            return None
        if isinstance(event.widget, tk.Entry):
            if dx:
                return None # Left / Right move the cursor in the text
            self.canvas.focus_set() # Up / Down leave the search box
        self.wakeHeader()
        controls = self.navControls()
        rects = {id(control): rect for control, rect in controls}
        target = self.navTarget
        if target is None or id(target) not in rects: # nothing chosen yet (or it went out of sight): start somewhere sensible
            target = self.navDefault(controls)
            if isinstance(target, GlassList) and dy:
                self.stepList(target, dy)
        elif isinstance(target, GlassList) and dy and self.stepList(target, dy):
            pass # moved to the next row
        elif isinstance(target, GlassSlider) and dx:
            self.nudgeSlider(target, dx)
        else:
            target = self.navNeighbour(controls, target, rects[id(target)], dx, dy) or target
        self.setNavTarget(target)
        return "break"

    def navDefault(self, controls):
        """Where the first arrow press lands: the tab's list, or its play button"""
        want = self.miniButtons["play"] if self.mini else {
            "library": self.listbox if self.listbox.items else self.playButton, "playlists": self.playlistList,
            "radio": self.stationList, "chill": self.chillButtons["play"], "settings": self.chooseButton,
        }.get(self.currentTab)
        for control, _ in controls:
            if control is want:
                return control
        return min(controls, key=lambda c: (c[1][1], c[1][0]))[0] if controls else None

    def navNeighbour(self, controls, current, rect, dx, dy):
        """The nearest control the arrow's way: past the chosen one's edge, and for Left / Right on the same side of
        the header's edge. Being off to the side counts twice as much as being far along"""
        header = {id(b) for b in (self.settingsButton, self.miniButton, self.shrinkButton, *self.tabButtons.values())}
        inHeader = id(current) in header
        cx, cy = (rect[0] + rect[2]) / 2, (rect[1] + rect[3]) / 2
        best, bestScore = None, None
        for control, (x0, y0, x1, y1) in controls:
            ox, oy = (x0 + x1) / 2 - cx, (y0 + y1) / 2 - cy
            if ox * dx + oy * dy <= 4:
                continue # not that way
            if (dx > 0 and x0 < rect[2] - 8 or dx < 0 and x1 > rect[0] + 8 or
                    dy > 0 and y0 < rect[3] - 8 or dy < 0 and y1 > rect[1] + 8):
                continue # mostly level with it (the expand arrow over the end of the list), not past it
            if dx and ((id(control) in header) != inHeader or y0 > rect[3] or y1 < rect[1]):
                continue # Left / Right stay on their row
            alongX, sideX = max(x0 - rect[2], rect[0] - x1, 0), max(y0 - rect[3], rect[1] - y1, 0) # gaps between the edges
            alongY, sideY = max(y0 - rect[3], rect[1] - y1, 0), max(x0 - rect[2], rect[0] - x1, 0)
            score = alongX + 2 * sideX + 0.02 * abs(oy) if dx else alongY + 2 * sideY + 0.02 * abs(ox)
            if bestScore is None or score < bestScore:
                best, bestScore = control, score
        return best

    @staticmethod
    def stepList(lst, step):
        """Moves the list's selection one row. False at either end (or when it is empty), so the arrow moves on"""
        if not lst.items:
            return False
        if lst.selected is None:
            lst.select(0)
            return True
        if 0 <= lst.selected + step < len(lst.items):
            lst.select(lst.selected + step)
            return True
        return False

    def nudgeSlider(self, slider, direction):
        """Left / Right move a slider: 5 seconds through the song, or a twentieth of the way for the others"""
        seek = slider in (self.seekBar, self.chillSeek)
        if seek and not self.active:
            return
        if slider.onPress:
            slider.onPress()
        slider.set(slider.get() + direction * (5 if seek else (slider.high - slider.low) / 20))
        if slider.command:
            slider.command(slider.value)
        if slider.onRelease:
            slider.onRelease()

    def setNavTarget(self, target):
        self.navTarget = target
        if isinstance(target, SearchBox):
            target.entry.focus_set() # so typing goes straight into it
        elif target is not None:
            self.canvas.focus_set() # so Delete and Ctrl+A reach the lists
        self.placeNavRing()

    def placeNavRing(self):
        """Puts the ring around the chosen control, or takes it away once that control is out of sight"""
        canvas, target = self.canvas, self.navTarget
        rect = self.navRect(target) if target is not None else None
        if rect is None:
            self.navTarget = None
        elif self.headerAlpha < 1 and target in (self.settingsButton, self.miniButton, self.shrinkButton, *self.tabButtons.values()):
            rect = None # the header is faded: the ring comes back with it
        if rect != self.navRingAt:
            self.navRingAt = rect
            if rect is None:
                canvas.coords(self.navRing, -9999, -9999)
                return
            pad = 4
            x0, y0, x1, y1 = rect
            radius = {GlassList: 18, SearchBox: 14, GlassCheck: 10}.get(type(target)) # their corners, plus the gap; None: a pill
            key = (int(x1 - x0) + 2 * pad, int(y1 - y0) + 2 * pad, radius)
            if key != self.navRingKey:
                photo = roundedImage(*key[:2], (0, 0, 0, 0), (255, 255, 255, 235), key[2])
                canvas.itemconfigure(self.navRing, image=photo)
                self.navRingPhoto, self.navRingKey = photo, key
            canvas.coords(self.navRing, x0 - pad, y0 - pad)
        if rect is not None:
            canvas.tag_raise(self.navRing) # over list rows drawn since

    def onReturn(self, event):
        if not self.keysAreOurs(event) or isinstance(event.widget, tk.Entry):
            return None
        target = self.navTarget
        second = bool(event.state & 0x1) # Shift+Enter: on the second channel
        if target is None: # no ring: Enter plays the list's selected row, as before
            lst = self.activeList()
            if lst:
                lst.activate(second)
        elif isinstance(target, tuple):
            self.applyTheme(target[0])
        elif isinstance(target, (GlassButton, GlassCheck)):
            target.command()
        elif isinstance(target, GlassList):
            target.activate(second)
        self.placeNavRing() # what it pressed may have moved or gone (another tab, mini mode)
        return "break"

    def onEscape(self, event):
        if self.keysAreOurs(event) and not isinstance(event.widget, tk.Entry) and self.lyricsOpen:
            self.closeLyrics()
        elif self.keysAreOurs(event) and not isinstance(event.widget, tk.Entry) and self.navTarget is not None:
            self.navTarget = None
            self.placeNavRing()
        elif self.keysAreOurs(event) and not isinstance(event.widget, tk.Entry) and self.fullscreen:
            self.setFullscreen(False)

    # ---- full screen (F11, and the Chill tab): a small box in the top right corner shrinks it back -----------------
    def toggleFullscreen(self):
        self.setFullscreen(not self.fullscreen)

    def tintTitleBars(self):
        """The title bars of the window and the open pop-ups in the theme colour, or with Title bar from picture ticked
        the background's average colour (again after Tk replaces a frame window)"""
        color = self.bgAverage if self.settings["pictureTitleBar"] else ACCENT
        self.dialogs = {win for win in self.dialogs if win.winfo_exists()}
        for window in (self.root, *self.dialogs):
            try:
                tintTitleBar(window, color)
            except Exception:
                pass # not Windows 11, or no DWM: Windows' own colours, then

    def setFullscreen(self, on):
        self.chillFullscreen = False # from here on it is the user's choice, which a tab change leaves alone
        if on == self.fullscreen:
            return
        self.fullscreen = on
        try:
            fill = fillMonitor(self.root) if on else None # the monitor it's on, read before Tk moves it to the main one
        except Exception:
            fill = None # the main monitor, then
        self.root.attributes("-fullscreen", on) # the new size arrives through <Configure>, which lays it all out again
        self.root.update_idletasks()
        if fill:
            fill()
        self.followFrame()

    def followFrame(self):
        """Going full screen, or into or out of mini mode, makes Tk replace the window's frame with a new one: the taskbar
        buttons and the title bar colour go onto the new one"""
        if self.thumbBar:
            self.thumbBar.follow(self.root)
        self.tintTitleBars()

    def onPointerPress(self, event):
        self.wakeHeader()
        if self.navTarget is not None: # back to the mouse: no ring
            self.navTarget = None
            self.placeNavRing()

    # ---- the Chill tab: the header fades away after 3 seconds without the mouse moving, and is back on any move -
    HEADER_IDLE = 3.0
    FADE_OUT, FADE_IN = 0.035, 0.14 # how much each 16 ms frame changes it: about half a second out, a tenth of one in

    def onPointerMove(self, event):
        spot = (event.x_root, event.y_root)
        if spot != self.lastPointer: # Windows also reports a "move" when a window changes under a still pointer
            self.lastPointer = spot
            self.wakeHeader()

    def wakeHeader(self):
        """The mouse moved or a key was pressed: the header comes back quickly, and the 3 seconds start again"""
        self.lastActivity = time.time()
        if self.headerTarget < 1:
            self.fadeHeaderTo(1.0)
        if self.headerIdleJob is None and self.currentTab == "chill" and not self.mini:
            self.headerIdleJob = self.root.after(int(self.HEADER_IDLE * 1000), self.headerIdle)

    def headerIdle(self):
        self.headerIdleJob = None
        if self.currentTab != "chill" or self.mini:
            return
        left = self.lastActivity + self.HEADER_IDLE - time.time()
        if left > 0.01: # it moved in the meantime: wait out the rest
            self.headerIdleJob = self.root.after(int(left * 1000) + 10, self.headerIdle)
        else:
            self.fadeHeaderTo(0.0)

    def resetHeader(self):
        """The header as itself again, straight away (a tab change, a resize)"""
        for job in (self.headerFadeJob, self.headerIdleJob):
            if job:
                self.root.after_cancel(job)
        self.headerFadeJob = self.headerIdleJob = None
        self.headerAlpha = self.headerTarget = 1.0
        self.canvas.itemconfigure(self.headerFadeItem, state="hidden", image="")
        self.headerFadePhoto = self.headerShot = None
        self.canvas.itemconfigure("full_header", state="hidden" if self.mini else "normal")
        self.wakeHeader()

    def fadeHeaderTo(self, target):
        self.headerTarget = target
        if self.headerAlpha >= 1 and target < 1 and not self.pictureHeader():
            self.headerAlpha = 0.0 # no picture to fade: it just goes
            self.canvas.itemconfigure("full_header", state="hidden")
            self.placeNavRing()
            return
        if self.headerFadeJob is None:
            self.headerFadeJob = self.root.after(16, self.headerFadeStep)

    def pictureHeader(self):
        """Swaps the header for a picture of it, which the fade makes more and more see-through. Fading one picture is
        far cheaper than redrawing every button, and looks exactly like the header"""
        canvas = self.canvas
        self.headerAlpha = 0.999 # takes the ring off a header button first, so it isn't in the picture
        self.placeNavRing()
        canvas.update_idletasks()
        try:
            shot = captureWindow(canvas)
        except Exception:
            shot = None
        box = canvas.bbox(self.panels["header"])
        if shot is None or not box:
            return False
        box = (max(box[0], 0), max(box[1], 0), min(box[2], shot.width), min(box[3], shot.height))
        shot = shot.crop(box)
        if shot.convert("L").getextrema()[1] == 0:
            return False # all black: Windows gave nothing
        self.headerShot = shot.convert("RGBA")
        photo = ImageTk.PhotoImage(shot)
        canvas.itemconfigure(self.headerFadeItem, image=photo, state="normal")
        self.headerFadePhoto = photo
        canvas.coords(self.headerFadeItem, box[0], box[1])
        canvas.tag_raise(self.headerFadeItem)
        canvas.itemconfigure("full_header", state="hidden")
        return True

    def headerFadeStep(self):
        self.headerFadeJob = None
        canvas, target = self.canvas, self.headerTarget
        if self.headerShot is None: # no picture: it simply shows again
            self.headerAlpha = target
        elif target > self.headerAlpha:
            self.headerAlpha = min(target, self.headerAlpha + self.FADE_IN)
        else:
            self.headerAlpha = max(target, self.headerAlpha - self.FADE_OUT)
        if self.headerAlpha >= 1: # all the way back: the real header again, so its buttons work and its clock ticks
            canvas.itemconfigure(self.headerFadeItem, state="hidden", image="")
            self.headerFadePhoto = self.headerShot = None
            canvas.itemconfigure("full_header", state="hidden" if self.mini else "normal")
            self.placeNavRing()
            return
        if self.headerShot is not None:
            self.headerShot.putalpha(int(255 * self.headerAlpha))
            photo = ImageTk.PhotoImage(self.headerShot)
            canvas.itemconfigure(self.headerFadeItem, image=photo, state="normal" if self.headerAlpha > 0 else "hidden")
            self.headerFadePhoto = photo
        if self.headerAlpha != target:
            self.headerFadeJob = self.root.after(16, self.headerFadeStep)

    def onResize(self, event):
        if (event.width, event.height) == self.laidOutSize and not self.resizeJob:
            return # already laid out for this size (the first one, when the window appears)
        if self.resizeJob:
            self.root.after_cancel(self.resizeJob)
        self.resizeJob = self.root.after(120, lambda: self.relayout(event.width, event.height)) # wait until dragging pauses

    def relayout(self, w, h):
        """Positions the header and the tab on screen for a w x h window; the other tabs are laid out when they are next
        shown. Panels are re-rendered from the blurred picture, so this is the expensive part of a resize (onResize
        waits until the window stops changing size)"""
        self.resizeJob = None
        if w < (60 if self.mini else 200) or h < (60 if self.mini else 200):
            return
        self.laidOutSize = (w, h)
        canvas = self.canvas
        if not self.fadeNextBackground: # (a new song's background leaves a faded Chill header faded)
            self.resetHeader()
        margin, gap = 16, 12

        # Background picture, scaled to cover the window and cropped around the middle
        fadeFrom, self.fadeNextBackground = self.bgCropped if self.fadeNextBackground else None, False
        if not self.bgSource:
            self.cancelBackgroundFade()
            self.bgBlur, self.bgFor, self.bgCropped = None, (None, None), None
            self.setBackgroundAverage(BG)
            self.playBackground(None, None, None)
        elif self.bgFor[0] is not self.bgSource or self.bgFor[1] != (w, h): # otherwise the last one still fits
            self.cancelBackgroundFade()
            iw, ih = self.bgSource.size
            scale = max(w / iw, h / ih)
            sw, sh = min(w / scale, iw), min(h / scale, ih) # the middle part of the picture that fills the window, in its pixels
            box = ((iw - sw) / 2, (ih - sh) / 2, (iw + sw) / 2, (ih + sh) / 2) # (min: rounding can make it a hair too big)
            cropped = self.bgSource.resize((w, h), Image.BILINEAR, box=box) # only that part is scaled, not the whole picture
            self.bgPhoto = ImageTk.PhotoImage(cropped)
            # a fade only where the picture is what you look at, and only between still pictures of the same size
            if (fadeFrom is not None and fadeFrom.size == cropped.size and self.backgroundShows() and not self.bgSource.animation
                    and self.root.state() != "iconic"):
                self.fadeBackground(fadeFrom, cropped, 1)
            else:
                canvas.itemconfigure(self.bgItem, image=self.bgPhoto)
            self.bgCropped = cropped
            small = cropped.resize((max(w // 4, 1), max(h // 4, 1)), Image.BILINEAR) # blurring a quarter-size copy is 16x cheaper
            r, g, b = small.resize((1, 1), Image.BOX).getpixel((0, 0)) # its average too: the same colour, 16x less to add up
            self.setBackgroundAverage(f"#{r:02x}{g:02x}{b:02x}")
            self.bgBlur = small.filter(ImageFilter.GaussianBlur(3.5)).resize((w, h), Image.BILINEAR)
            self.bgFor = (self.bgSource, (w, h))
            self.playBackground(self.bgSource.animation, (w, h), box)

        if self.mini:
            self.layoutMini(w, h)
            return

        inset = margin + 16 # the title and tabs sit this far in from the header's left edge, the Settings button from its right edge
        self.title.place(inset, 28)
        self.headerVis = (inset + self.titleWidth + 16, 40, 24) # left edge, baseline, tallest bar
        self.headerVis2 = (self.headerVis[0] + VIS_BARS * 5 + 14, 40, 24) # channel two's, just after it
        right = w - inset - (42 if self.fullscreen else 0) # full screen: the shrink box takes the corner
        if self.fullscreen:
            self.shrinkButton.place(w - inset - 34, 12, 34, 32)
        else:
            self.shrinkButton.place(-9999, -9999, 34, 32)
        self.settingsButton.place(right - 104, 12, 104, 32)
        self.miniButton.place(right - 104, 46, 104, 34)
        self.clock.place(right - 104 - 14, 28)
        # rows are centred in the header (8 px above the top row, 8 px below the tabs)
        self.tabButtons["library"].place(inset, 46, 104, 34)
        visCenter = self.headerVis[0] + 2 + ((VIS_BARS - 1) * 5 + 3) / 2 # the Playlists button sits right under the visualizer
        playlistsX = max(int(visCenter - 58), inset + 112)
        self.tabButtons["playlists"].place(playlistsX, 46, 116, 34)
        gapX = playlistsX - (inset + 104) # the gap between Library and Playlists, used between all the tabs
        radioX = playlistsX + 116 + gapX
        self.tabButtons["radio"].place(radioX, 46, 96, 34)
        self.tabButtons["chill"].place(radioX + 96 + gapX, 46, 96, 34)

        top, contentW, contentH = 94, w - 2 * margin, h - 94 - margin

        panel = self.panel
        panel("header", margin, 4, contentW, 84, 24)

        self.libGeometry = (margin, gap, top, contentW, contentH) # the area under the header, shared by every tab
        self.tabGeometry = (w, h)
        self.dirtyTabs = set(self.TAB_LAYOUTS) # every tab is placed again, but each only when it is next shown
        self.layoutTab(self.currentTab)
        canvas.tag_lower("panel")
        canvas.tag_lower(self.bgItem)
        self.applyTabVisibility()
        self.updateVisBox()

    # ---- each tab's layout, done only for the tab on screen (a resize used to re-render the glass of every tab) --
    TAB_LAYOUTS = ("library", "playlists", "radio", "chill", "settings")

    def layoutTab(self, name):
        """Lays out a tab for the current window size, unless that was already done"""
        if name in self.dirtyTabs:
            self.dirtyTabs.discard(name)
            getattr(self, "layout" + name.capitalize() + "Tab")()

    def layoutLibraryTab(self):
        canvas = self.canvas
        self.placeLibrary()
        for item in (self.veil, self.panels["songs"], self.libraryLabel.item, self.listbox.tag, f"bar{id(self.listbox)}", self.search.back,
                     *(f"button{id(b)}" for b in (*self.sortButtons.values(), self.arrowButton))): # the open library sits over the veil
            canvas.tag_raise(item)

    def layoutPlaylistsTab(self):
        margin, gap, top, contentW, contentH = self.libGeometry
        leftW = int(contentW * 0.36)
        rightX, rightW = margin + leftW + gap, contentW - leftW - gap
        panel = self.panel
        panel("playlists", margin, top, leftW, contentH)
        panel("tracks", rightX, top, rightW, contentH)
        self.playlistsLabel.place(margin + 18, top + 37)
        self.playlistAdd.place(margin + leftW - 14 - 44, top + 20, 44, 34)
        self.playlistSearch.place(margin + 12, top + 62, leftW - 24, self.bgBlur) # level with the songs' search box
        self.playlistList.place(margin + 12, top + 100, leftW - 24, contentH - 112)
        self.tracksLabel.place(rightX + 18, top + 37)
        self.addSongsButton.place(rightX + rightW - 14 - 130, top + 20, 130, 34)
        if self.settings["youtube"]: # the add-a-YouTube-song button sits just left of Add songs...
            self.playlistYouTubeButton.place(rightX + rightW - 14 - 130 - 6 - self.YT_W, top + 20, self.YT_W, 34)
        else:
            self.playlistYouTubeButton.place(-9999, -9999, self.YT_W, 34)
        self.trackSearch.place(rightX + 12, top + 62, rightW - 24, self.bgBlur)
        x = rightX + 12
        for (mode, _), width in zip(LIST_SORT_MODES, (64, 62, 46, 64, 64)): # Added | Name | # | Album | Artist
            self.playlistSortButtons[mode].place(x, top + 100, width, 28)
            x += width + 4
        self.trackList.place(rightX + 12, top + 136, rightW - 24, contentH - 136 - 62)
        self.playlistStatus.place(rightX + 18, top + contentH - 46, rightW - 36)

    def layoutRadioTab(self):
        margin, _, top, contentW, contentH = self.libGeometry
        panel = self.panel
        panel("radio", margin, top, contentW, contentH)
        self.stationsLabel.place(margin + 22, top + 38)
        self.addButton.place(margin + contentW - 22 - 44, top + 21, 44, 34)
        self.removeButton.place(margin + contentW - 22 - 44 - 8 - 96, top + 21, 96, 34)
        self.stationList.place(margin + 16, top + 70, contentW - 32, contentH - 70 - 70)
        self.radioStatus.place(margin + 22, top + contentH - 56, contentW - 44)

    def layoutChillTab(self):
        w, h = self.tabGeometry
        self.layoutChill(self.libGeometry[0], w, h)

    def layoutSettingsTab(self):
        margin, _, top, contentW, contentH = self.libGeometry
        self.panel("settings", margin, top, contentW, contentH)
        self.placeSettings()

    # ---- settings page: its rows, scrolled inside the panel when the window is too short for them ------------------
    SETTINGS_EDGE = 14 # rows only show while they are wholly this far inside the panel
    CHECK_TEXT = 200 # where a tick box's explanation starts, so they all line up
    SCROLL_STEP = 60 # pixels per notch of the mouse wheel

    def placeSettings(self):
        """Places every setting for the current scroll position. A canvas can't cut items off at the panel's edge, so a
        row that isn't wholly inside the panel is hidden (clipSettings). Placing is cheap: the panel itself isn't redrawn"""
        margin, _, top, contentW, contentH = self.libGeometry
        canvas = self.canvas
        x, ww = margin + 26, contentW - 52 - 12 # room for the scroll bar on the right
        y = top + 26 - self.settingsScroll
        bands = [] # (top, bottom) of each row, so a row is shown or hidden as a whole

        def check(box, text): # a tick box with its explanation beside it
            box.place(x, y)
            text.place(x + self.CHECK_TEXT, y + 17, ww - self.CHECK_TEXT)
            bands.append((y, y + 34))

        self.settingsHeader.place(x, y)
        bands.append((y, y + 18))
        y += 28
        self.dayLabel.place(x + 32, y + 17)
        self.bgName.place(x + 100, y + 17, ww - 320 - 100)
        self.chooseButton.place(x + ww - 306, y, 170, 34)
        self.defaultBgButton.place(x + ww - 126, y, 126, 34)
        bands.append((y, y + 34))
        y += 42
        self.nightCheck.place(x, y)
        self.nightName.place(x + 100, y + 17, ww - 320 - 100)
        self.nightChooseButton.place(x + ww - 306, y, 170, 34)
        self.nightDefaultButton.place(x + ww - 126, y, 126, 34)
        bands.append((y, y + 34))
        y += 42
        check(self.coverCheck, self.coverText)
        y += 54

        self.themeHeader.place(x, y)
        bands.append((y, y + 18))
        y += 28
        for i, (color, item) in enumerate(self.swatches):
            canvas.coords(item, x + 4 + i * 42, y + 2, x + 4 + i * 42 + 30, y + 32)
        self.customColor.place(x + 4 + len(self.swatches) * 42 + 8, y, 110, 34)
        self.markSwatch()
        bands.append((y - 4, y + 36)) # the ring round the chosen colour sticks out a little
        y += 42
        check(self.pictureTitleBarCheck, self.titleBarText)
        y += 54

        self.extrasHeader.place(x, y)
        bands.append((y, y + 18))
        y += 28
        check(self.funCheck, self.funText)
        y += 42
        check(self.youtubeCheck, self.youtubeText)
        y += 42
        self.languageLabel.place(x + 32, y + 17)
        self.languageButton.place(x + self.CHECK_TEXT - 70, y, 170, 34) # (its explanation starts after it)
        self.languageText.place(x + self.CHECK_TEXT + 112, y + 17, ww - self.CHECK_TEXT - 112)
        bands.append((y, y + 34))
        y += 54

        colW = (ww - 40) // 2 # equalizer on the left, fades beside it
        x2 = x + colW + 40
        self.eqHeader.place(x, y)
        self.fadeHeader.place(x2, y)
        bands.append((y, y + 18))
        y += 34
        rowsTop = y
        for label, slider, readout in self.eqRows.values():
            label.place(x, y + 11)
            slider.place(x + 80, y, colW - 80 - 76)
            readout.place(x + colW, y + 11)
            bands.append((y - 4, y + 30))
            y += 46
        for i, (label, slider, readout) in enumerate(self.fadeRows.values()):
            label.place(x2, rowsTop + i * 46 + 11)
            slider.place(x2 + 80, rowsTop + i * 46, colW - 80 - 76)
            readout.place(x2 + colW, rowsTop + i * 46 + 11)
        self.settingsStatus.place(x2, rowsTop + 2 * 46 + 8, colW) # (in the third row's band: the fades only have two)
        self.eqReset.place(x + colW - 110, y + 6, 110, 34)
        self.fadeReset.place(x2 + colW - 110, y + 6, 110, 34)
        bands.append((y + 6, y + 40))
        y += 40 + 22

        # how far it can scroll: the page's full height against the room the panel has
        viewTop, viewBottom = top + self.SETTINGS_EDGE, top + contentH - self.SETTINGS_EDGE
        self.settingsMaxScroll = max(0, y + self.settingsScroll - (top + contentH))
        if self.settingsScroll > self.settingsMaxScroll: # the window grew: no empty space left under the page
            self.settingsScroll = self.settingsMaxScroll
            self.placeSettings()
            return
        self.settingsBands, self.settingsView = bands, (viewTop, viewBottom)
        barX = margin + contentW - 14
        canvas.coords(self.settingsTrack, barX, viewTop + 4, barX, viewBottom - 4)
        if self.settingsMaxScroll:
            span = viewBottom - viewTop - 8
            length = max(30, span * (contentH / (contentH + self.settingsMaxScroll)))
            start = viewTop + 4 + (span - length) * self.settingsScroll / self.settingsMaxScroll
            canvas.coords(self.settingsThumb, barX, start, barX, start + length)
        if self.currentTab == "settings":
            self.clipSettings()

    def clipSettings(self):
        """Shows the rows wholly inside the panel and hides the rest, and the scroll bar only when there's more page"""
        canvas = self.canvas
        viewTop, viewBottom = self.settingsView
        skip = {self.panels["settings"], self.settingsTrack, self.settingsThumb}
        for item in canvas.find_withtag("tab_settings"):
            if item in skip:
                continue
            ys = canvas.coords(item)[1::2]
            if not ys:
                continue
            spot = sum(ys) / len(ys) # where the item is: its anchor point, or the middle of a line or circle
            band = next(((b0, b1) for b0, b1 in self.settingsBands if b0 - 2 <= spot <= b1 + 2), (spot, spot))
            shown = band[0] >= viewTop and band[1] <= viewBottom
            canvas.itemconfigure(item, state="normal" if shown else "hidden")
        canvas.itemconfigure("settingsbar", state="normal" if self.settingsMaxScroll else "hidden")
        if self.navTarget is not None:
            self.placeNavRing() # its control may have just scrolled out of sight

    def scrollSettings(self, pixels):
        scroll = min(max(self.settingsScroll + pixels, 0), self.settingsMaxScroll)
        if scroll != self.settingsScroll:
            self.settingsScroll = scroll
            self.placeSettings()

    def onSettingsTrack(self, event):
        """A click on the bar above or below its thumb moves a page that way"""
        _, start, _, end = self.canvas.coords(self.settingsThumb)
        page = self.settingsView[1] - self.settingsView[0] - 40
        if event.y < start:
            self.scrollSettings(-page)
        elif event.y > end:
            self.scrollSettings(page)

    def onSettingsThumbDown(self, event):
        self.thumbGrab = (event.y, self.settingsScroll)

    def onSettingsThumbDrag(self, event):
        grabY, grabScroll = self.thumbGrab
        _, start, _, end = self.canvas.coords(self.settingsThumb)
        free = (self.settingsView[1] - self.settingsView[0] - 8) - (end - start) # how far the thumb can travel
        if free > 0:
            self.scrollSettings(grabScroll + (event.y - grabY) * self.settingsMaxScroll / free - self.settingsScroll)

    # ---- the Chill tab: just the song and its buttons, along the bottom of the window ------------------------------
    CHILL_SIZE = (560, 112) # the panel's largest width, and its height
    ART_CHILL = 64

    def updateVisBox(self):
        """The visualizer sits in the header, down in the Chill panel beside the song name, or in the mini window"""
        self.visBox = self.miniVis if self.mini else self.chillVis if self.currentTab == "chill" else self.headerVis
        self.visBox2 = self.miniVis2 if self.mini else self.chillVis2 if self.currentTab == "chill" else self.headerVis2
        self.drawVis() # the loop may be asleep, so move the bars now

    CHILL_SPACE = 24 # between the two players' panels

    def layoutChill(self, margin, w, h):
        height = self.CHILL_SIZE[1]
        if self.dual: # two panels side by side, the pair centred
            width = min(self.CHILL_SIZE[0], (w - 2 * margin - self.CHILL_SPACE) // 2)
            x = (w - 2 * width - self.CHILL_SPACE) // 2
            self.chillBox = (x, h - 28 - height, width, height)
            self.chillBox2 = (x + width + self.CHILL_SPACE, h - 28 - height, width, height)
            self.panel("chill2", *self.chillBox2, radius=22, alpha=70)
        else:
            width = min(w - 2 * margin, self.CHILL_SIZE[0]) # a modest panel in the middle, so most of the picture shows
            self.chillBox = ((w - width) // 2, h - 28 - height, width, height)
            self.canvas.coords(self.panels["chill2"], -9999, -9999)
        self.panel("chill", *self.chillBox, radius=22, alpha=70) # far more see-through than the other panels (195)
        self.placeChill()
        self.placeChill2()

    def placeChill(self):
        """Cover (when the song has one) at the left; to its right the song name with the visualizer at the end of the
        line, a thin progress line, and the three buttons"""
        if "chill" in self.dirtyTabs:
            return # done when the tab is next shown
        x, y, width, height = self.chillBox
        pad = 22
        left = x + pad + (self.ART_CHILL + 16 if self.artPhotos else 0)
        right = x + width - pad
        self.canvas.coords(self.chillArtItem, x + pad if self.artPhotos else -9999, y + (height - self.ART_CHILL) // 2)
        self.chillTextWidth = right - left - 70 - 14
        self.chillShadow.place(left + 1, y + 17)
        self.chillTitle.place(left, y + 16)
        self.chillVis = (right - 70, y + 38, 24) # level with the song name, at the end of its line
        self.chillSeek.place(left - 9, y + 46, right - left + 18)
        for i, button in enumerate(self.chillButtons.values()):
            button.place(left + (right - left - 3 * 52 - 2 * 8) / 2 + i * 60, y + height - 16 - 30, 52, 30)
        self.placeChillLyrics(1, self.chillBox, right, y + height - 16 - 30)
        self.placeChillVolume(1, left + (right - left - 3 * 52 - 2 * 8) / 2 + 2 * 60 + 52, right, y + height - 16 - 30)
        self.updateVisBox()
        self.chillShown = None
        self.syncChill()

    def syncChill(self):
        """Keeps the Chill tab in step with the player: the song name (cut to one line) and the play / pause symbol.
        Only while the tab is showing, and only when something changed"""
        if self.currentTab != "chill" or self.mini:
            return
        name = self.titleText
        playing = self.active and not self.player.paused
        state = (name, self.chillTextWidth, playing)
        if state == self.chillShown:
            return
        self.chillShown = state
        if self.chillFont.measure(name) > self.chillTextWidth: # one line only: cut it short rather than let it wrap
            while name and self.chillFont.measure(name + "...") > self.chillTextWidth:
                name = name[:-1]
            name = name.rstrip() + "..."
        self.chillTitle.configure(text=name)
        self.chillShadow.configure(text=name)
        self.chillButtons["play"].configure(text="❚❚" if playing else "⏵")

    def placeChill2(self):
        """The second player's Chill panel: the first's layout, without the visualizer"""
        if "chill" in self.dirtyTabs or not self.dual:
            return
        x, y, width, height = self.chillBox2
        pad = 22
        left = x + pad + (self.ART_CHILL + 16 if self.art2Photos else 0)
        right = x + width - pad
        self.canvas.coords(self.chill2ArtItem, x + pad if self.art2Photos else -9999, y + (height - self.ART_CHILL) // 2)
        self.chill2TextWidth = right - left - 70 - 14
        self.chillVis2 = (right - 70, y + 38, 24) # at the end of the song name's line, as in the first panel
        self.chill2Shadow.place(left + 1, y + 17)
        self.chill2Title.place(left, y + 16)
        self.chill2Seek.place(left - 9, y + 46, right - left + 18)
        for i, button in enumerate(self.chill2Buttons.values()):
            button.place(left + (right - left - 3 * 52 - 2 * 8) / 2 + i * 60, y + height - 16 - 30, 52, 30)
        self.placeChillLyrics(2, self.chillBox2, right, y + height - 16 - 30)
        self.placeChillVolume(2, left + (right - left - 3 * 52 - 2 * 8) / 2 + 2 * 60 + 52, right, y + height - 16 - 30)
        self.chill2Shown = None
        self.syncChill2()

    def syncChill2(self):
        if self.currentTab != "chill" or self.mini or not self.dual:
            return
        state = (self.title2Text, self.chill2TextWidth)
        if state == self.chill2Shown:
            return
        self.chill2Shown = state
        name = fitText(self.chillFont, self.title2Text, self.chill2TextWidth)
        self.chill2Title.configure(text=name)
        self.chill2Shadow.configure(text=name)

    # ---- mini mode: a small window with the song name, prev / play / next and mute --------------------------------
    MINI_SIZE = (520, 116) # (wide enough for each row's volume bar between its buttons and its visualizer)
    MINI_SECOND = 92 # how much taller mini mode grows for the second player's row
    ART_BIG, ART_SMALL, ART_COMPACT = 56, 64, 44
    ART_COMPACT_DROP = 18 # the narrow players' covers sit this far down, clear of channel two's close button

    def toggleMini(self):
        root = self.root
        if not self.mini:
            self.setFullscreen(False) # mini mode is a small window, never a full screen one
            self.wasMaximized = root.state() == "zoomed"
            if self.wasMaximized:
                root.state("normal") # nor a maximized one: Windows would keep it filling the screen
            root.update_idletasks() # so the size kept below is the window's own, not the screen's
            self.normalSize = root.geometry()
            self.mini = True
            self.showTab("mini")
            size = self.miniWanted()
            root.minsize(*size)
            root.resizable(False, False) # one fixed size
            root.geometry("%dx%d" % size)
            root.attributes("-topmost", True) # stays in front of every other window, even when another one is in use
        else:
            self.mini = False
            root.attributes("-topmost", False)
            root.resizable(True, True)
            root.minsize(*self.MIN_SIZE)
            root.geometry(self.normalSize)
            self.showTab(self.lastTab)
            size = tuple(int(n) for n in self.normalSize.split("+")[0].split("x"))
            if self.wasMaximized:
                root.state("zoomed") # maximized again, as it was before mini mode
            if self.fullscreen or self.wasMaximized: # back to the Chill tab, which went full screen, or to a maximized window
                root.update_idletasks()
                size = (root.winfo_width(), root.winfo_height())
        self.miniShown = None
        self.relayout(*size) # straight away, so the old layout is never seen in the new window
        self.syncMini()
        self.followFrame()

    def miniWanted(self):
        """Mini mode's size: one row of controls, or two while channel two is in use"""
        w, h = self.MINI_SIZE
        return (w, h + (self.MINI_SECOND if self.dual else 0))

    def resizeMini(self):
        """Channel two came or went while in mini mode: the window grows downward for its row, or shrinks back"""
        size = self.miniWanted()
        self.root.minsize(*size)
        self.root.geometry("%dx%d" % size)
        self.relayout(*size)
        self.followFrame()

    def layoutMini(self, w, h):
        canvas = self.canvas
        self.miniSize = (w, h)
        self.panel("mini", 8, 8, w - 16, h - 16, 18)
        self.placeMini()
        canvas.tag_lower("panel")
        canvas.tag_lower(self.bgItem)
        self.applyTabVisibility()

    def placeMini(self):
        """Puts the mini controls in place: the cover (when the song has one) takes the left end"""
        w, _ = self.miniSize
        h = self.MINI_SIZE[1] # the first row keeps its place when the window grows for the second
        right = w - 26
        left = 26 + (self.ART_SMALL + 12 if self.artPhotos else 0)
        self.canvas.coords(self.miniArtItem, 26 if self.artPhotos else -9999, (h - self.ART_SMALL) // 2)
        self.miniExit.place(right - 28, 20, 28, 26)
        self.miniTextWidth = right - left - 28 - 12
        self.miniTitle.place(left, 24)
        top = h - 22 - 34
        for i, button in enumerate(self.miniButtons.values()):
            button.place(left + i * 58, top, 50, 34)
        self.miniVis = (right - 70, top + 28, 24) # the visualizer takes the right-hand end of the button row
        self.placeMiniVolume(1, left + 3 * 58 + 50, right - 70, top)
        self.updateVisBox()
        self.miniShown = None
        self.syncMini()
        if self.dual: # channel two's row: the same layout, one row lower
            dy = self.MINI_SECOND
            left2 = 26 + (self.ART_SMALL + 12 if self.art2Photos else 0)
            self.canvas.coords(self.mini2Line, 26, h - 6, right, h - 6)
            self.canvas.coords(self.mini2ArtItem, 26 if self.art2Photos else -9999, (h - self.ART_SMALL) // 2 + dy)
            self.mini2TextWidth = right - left2
            self.miniVis2 = (right - 70, top + dy + 28, 24) # the right-hand end of its button row, as in the first row
            self.mini2Title.place(left2, 24 + dy)
            for i, button in enumerate(self.mini2Buttons.values()):
                button.place(left2 + i * 58, top + dy, 50, 34)
            self.placeMiniVolume(2, left2 + 3 * 58 + 50, right - 70, top + dy)
            self.mini2Shown = None
            self.syncMini2()
            self.updateVisBox()

    def placeMiniVolume(self, channel, start, end, top):
        """A mini row's volume bar: in the space between the end of its buttons and its visualizer, up to 130 px"""
        width = min(end - 14 - (start + 14), 130)
        self.miniVolumes[channel].place(end - 14 - width, top + 6, width) # (the bar's 22 px, in the middle of the 34 px buttons)

    def showArt(self, path):
        """Shows the cover of the song that just started (or nothing, when it has none) in the player and in mini mode"""
        key = os.path.normcase(str(path)) if path else None
        if key == self.artPath:
            return
        self.artPath = key
        data = readArt(path) if path else None
        self.artData = data
        if self.settings["cover"]:
            self.applyBackground(fade=True)
        try:
            self.artPhotos = (artImage(data, self.ART_BIG, 10), artImage(data, self.ART_SMALL, 10),
                              artImage(data, self.ART_COMPACT, 8)) if data else None
        except Exception:
            self.artPhotos = None # not a picture it can read
        self.canvas.itemconfigure(self.artItem, image=self.artPhotos[2 if self.compact else 0] if self.artPhotos else "")
        self.canvas.itemconfigure(self.miniArtItem, image=self.artPhotos[1] if self.artPhotos else "")
        self.canvas.itemconfigure(self.chillArtItem, image=self.artPhotos[1] if self.artPhotos else "") # the same 64 px picture as mini mode
        self.placeArt()
        self.placeChill()
        if self.mini:
            self.placeMini()

    def placeArt(self):
        """The cover sits at the right end of the song name's row, above the progress bar, and the name makes room for it"""
        x, y, ww = self.nowBox
        if self.artPhotos:
            size = self.ART_COMPACT if self.compact else self.ART_BIG
            self.canvas.coords(self.artItem, x + ww - size, y + (self.ART_COMPACT_DROP if self.compact else 0))
        else:
            self.canvas.coords(self.artItem, -9999, -9999)
        self.placeTitle()

    def placeTitle(self):
        """A song name that fits on one line is centred between the top of the box and the progress bar; a longer one
        wraps and starts at the top, as there is no room to centre it. One so long that it would run down into the
        progress bar is cut short with "..." to the lines that fit (how many depends on the window's size)"""
        x, y, ww = self.nowBox
        width = max(ww - ((self.ART_COMPACT if self.compact else self.ART_BIG) + 14 if self.artPhotos else 0), 40)
        lines = max(1, int((self.titleZone[1] - y) // self.titleFont.metrics("linespace")))
        text = fitLines(self.titleFont, self.titleText, width - 2, lines) # (2 px spare: Tk's own measuring may differ a hair)
        self.nowPlaying.configure(text=text)
        if self.titleFont.measure(text) <= width:
            top, bottom = self.titleZone
            y = (top + bottom - self.titleFont.metrics("linespace")) / 2
        self.nowPlaying.place(x, y, width)

    def syncMini(self):
        """Keeps the mini controls in step with the player: song name, play / pause symbol, muted or not"""
        if not self.mini:
            return
        name = self.titleText
        playing = self.active and not self.player.paused
        state = (name, self.miniTextWidth, playing, self.player.muted)
        if state == self.miniShown:
            return
        self.miniShown = state
        if self.miniFont.measure(name) > self.miniTextWidth: # one line only: cut it short rather than let it wrap
            while name and self.miniFont.measure(name + "...") > self.miniTextWidth:
                name = name[:-1]
            name = name.rstrip() + "..."
        self.miniTitle.configure(text=name)
        self.miniButtons["play"].configure(text="❚❚" if playing else "⏵")
        self.miniButtons["mute"].configure(text="🔇" if self.player.muted else "🔊", style="Accent.TButton" if self.player.muted else "TButton")

    def syncMini2(self):
        if not self.mini or not self.dual:
            return
        state = (self.title2Text, self.mini2TextWidth, self.player2.muted)
        if state == self.mini2Shown:
            return
        self.mini2Shown = state
        self.mini2Title.configure(text=fitText(self.miniFont, self.title2Text, self.mini2TextWidth))
        self.mini2Buttons["mute"].configure(text="🔇" if self.player2.muted else "🔊",
                                            style="Accent.TButton" if self.player2.muted else "TButton")

    def panel(self, name, x, y, pw, ph, radius=20, alpha=195):
        """Renders one frosted glass panel for its current place and size (alpha: how solid it is, out of 255)"""
        self.panelPhotos[name] = frostedImage(self.bgBlur, x, y, pw, ph, radius, alpha)
        self.canvas.itemconfigure(self.panels[name], image=self.panelPhotos[name])
        self.canvas.coords(self.panels[name], x, y)

    # ---- library panel: the arrow button widens it over a blurred player, and narrows it again ------------------
    SORT_WIDTHS = (64, 62, 46, 64, 64) # Added | Name | # | Album | Artist
    ARROW_W = 34
    YT_W = 46 # the +YT button

    def libraryWidths(self):
        """(resting width, current width) of the song panel"""
        contentW = self.libGeometry[3]
        rest = int(contentW * 0.36)
        allButtons = sum(self.SORT_WIDTHS) + 4 * len(self.SORT_WIDTHS) + self.ARROW_W + 24 # every filter button and the arrow
        wide = min(max(self.rowWidth + 72, rest, allButtons), contentW) # wide enough for the longest row and all the buttons
        return rest, wide if self.libOpen else rest

    def veilImage(self, x, y, w, h, alpha, radius=20):
        """Frosted sheet over the player: the blurred picture, darkened, more opaque the further the library is open"""
        outer = roundedMask(w, h, radius)
        if self.bgBlur is None:
            sheet = Image.new("RGBA", (w, h), (12, 14, 20, 255))
        else:
            sheet = self.bgBlur.crop((int(x), int(y), int(x) + w, int(y) + h)).convert("RGBA")
            sheet = Image.blend(sheet, Image.new("RGBA", sheet.size, (12, 14, 20, 255)), 0.55)
        sheet.putalpha(outer.point(lambda v: v * alpha // 255))
        return ImageTk.PhotoImage(sheet)

    def placeLibrary(self):
        """Lays out the song panel at its current openness. The player stays put underneath and is veiled as the panel opens"""
        margin, gap, top, contentW, contentH = self.libGeometry
        restW, leftW = self.libraryWidths()
        self.libWidthsShown = (restW, leftW)
        rightX, rightW = margin + restW + gap, contentW - restW - gap
        self.panel("songs", margin, top, leftW, contentH)
        # top row: the search box and the expand/collapse arrow. Below it: the filter buttons
        self.arrowButton.place(margin + leftW - 12 - self.ARROW_W, top + 14, self.ARROW_W, 30)
        self.arrowButton.configure(text="←" if self.libOpen else "→")
        fieldW = leftW - 24 - self.ARROW_W - 6
        if self.settings["youtube"]: # the add-a-YouTube-song button sits between the search box and the arrow
            fieldW -= self.YT_W + 6
            self.youtubeButton.place(margin + 12 + fieldW + 6, top + 14, self.YT_W, 30)
        else:
            self.youtubeButton.place(-9999, -9999, self.YT_W, 30)
        self.search.place(margin + 12, top + 14, fieldW, self.bgBlur)
        x, room = margin + 12, leftW - 24 # the filter buttons only show once the library is expanded
        for (mode, _), width in zip(LIST_SORT_MODES, self.SORT_WIDTHS):
            if self.libOpen and x - (margin + 12) + width <= room:
                self.sortButtons[mode].place(x, top + 52, width, 28)
                x += width + 4
            else:
                self.sortButtons[mode].place(-9999, -9999, width, 28)
        listTop = 88 if self.libOpen else 52 # no filter row to make room for while collapsed
        self.listbox.place(margin + 12, top + listTop, leftW - 24, contentH - listTop - 38)
        self.libraryLabel.place(margin + 18, top + contentH - 28, leftW - 30)
        if self.libOpen:
            self.veilPhoto = self.veilImage(rightX, top, rightW, contentH, 235)
            self.canvas.itemconfigure(self.veil, image=self.veilPhoto)
            self.canvas.coords(self.veil, rightX, top)
        else:
            self.canvas.coords(self.veil, -9999, -9999)
        self.updateLibraryLabel()

        self.playerArea = (rightX, rightW, top, contentH, gap)
        self.placePlayers()

    # ---- the library page's players: one across the whole right side, or (channel two in use) two side by side ---
    # Opening the second player squeezes the first to the left while the second's panel grows in from the right
    # (closing runs it backwards). The voice row and the message box stay where they are, on a panel of their own
    # under both players
    DUAL_MS = 320 # how long the panels take to move
    VOICE_ROW = 282 # from the top of the player panel down to the voice row

    LYRICS_H = 88 # the lyrics strip under each player (and how far it moves the voice row down)

    def lyricsBand(self):
        """Whether the library page makes room for lyrics under its players: a song with lyrics is playing on one"""
        return bool(self.lyrics[1] or (self.dual and self.lyrics[2]))

    def placePlayers(self):
        rightX, rightW, top, contentH, gap = self.playerArea
        t, pad = self.dualT, 22
        band = self.LYRICS_H if self.lyricsBand() else 0
        voiceY = top + self.VOICE_ROW + band
        half = (rightW - gap) / 2
        if t <= 0:
            self.panel("player", rightX, top, rightW, contentH)
            for name in ("player2", "voice"):
                self.canvas.coords(self.panels[name], -9999, -9999)
            self.placePlayer1(rightX, top, rightW, 0.0)
        else:
            split = top + self.VOICE_ROW - 14 # where the voice panel starts (the lyrics are at its top)
            w1, w2 = round(rightW - t * (rightW - half)), round(t * half)
            height = round(split - gap * t - top) # the gap above the voice panel opens up as they part
            self.panel("player", rightX, top, w1, height)
            if w2 >= 30:
                self.panel("player2", rightX + rightW - w2, top, w2, height)
            else:
                self.canvas.coords(self.panels["player2"], -9999, -9999)
            self.panel("voice", rightX, split, rightW, top + contentH - split)
            self.placePlayer1(rightX, top, w1, t)
            if t >= 1:
                self.placePlayer2(rightX + rightW - w2, top, w2)
        bandY = top + self.VOICE_ROW - 16 + 10 * t # under the volume row; a little lower once it's on the voice panel
        width1 = rightW if t <= 0 else round(rightW - t * (rightW - half))
        self.placeLyricsStrip(1, rightX + pad, bandY, width1 - 2 * pad, band)
        self.placeLyricsStrip(2, rightX + rightW - half + pad, bandY, half - 2 * pad, band if t >= 1 else 0)
        self.placeLyricsView()
        x, ww, y = rightX + pad, rightW - 2 * pad, voiceY
        if self.voiceAvailable:
            self.voiceLabel.place(x, y + 17)
            self.voiceButton.place(x + ww - 124, y, 124, 34)
            self.voiceInfoSpot = (x + ww - 124 - 8 - 34, y)
            y += 46
        else: # voice isn't installed: no row for it, and the message box gets the room
            self.voiceLabel.place(-9999, -9999)
            self.voiceButton.place(-9999, -9999, 124, 34)
            self.voiceInfoSpot = None
        self.log.place(x, y, ww, max(top + contentH - pad - y, 20))
        self.placeVoiceInfo()

    def placeVoiceInfo(self):
        """The i button sits just left of the voice button, and only while voice is on"""
        if self.voiceOn and self.voiceInfoSpot:
            self.voiceInfoButton.place(*self.voiceInfoSpot, 34, 34)
        else:
            self.voiceInfoButton.place(-9999, -9999, 34, 34)

    def placeLyricsStrip(self, channel, x, y, w, h):
        """A player's lyrics, centred under it, with ⤢ at the right to open them all. Nothing without lyrics"""
        strip, button = self.libLyrics[channel], self.lyricsButtons[channel]
        if not h or not self.lyrics[channel]:
            strip.place(-9999, -9999, 0, 0)
            button.place(-9999, -9999, 26, 22)
            return
        button.place(x + w - 26, y + h / 2 - 11, 26, 22)
        strip.place(x + 32, y, w - 64, h) # the same margin on both sides keeps the lines centred under the player

    def placePlayer1(self, px, top, pw, t):
        """The first player at this width. t (how far it is into the two-player layout) also draws the rows a little
        closer, so the narrower player still fits above the voice row. Buttons share out the width they have"""
        pad = 22
        x, ww, y = px + pad, pw - 2 * pad, top + pad
        self.nowBox = (x, y, ww)
        self.titleZone = (top, y + 74 + 4) # the progress knob starts 4 px into its row
        self.placeArt()
        y += 74 # the progress knob ends up as far below the cover as the cover is below the panel's top edge
        self.elapsed.place(x, y + 11)
        self.total.place(x + ww, y + 11)
        self.seekBar.place(x + 40, y, ww - 80)
        y += 38
        space = 10 - 4 * t
        bw, bh = min(104, (ww - 2 * space) / 3), 38 - 4 * t
        start = x + (ww - (3 * bw + 2 * space)) / 2
        for i, button in enumerate((self.prevButton, self.playButton, self.nextButton)):
            button.place(start + i * (bw + space), y, bw, bh)
        y += bh + 2
        sw = min(96, (ww - 2 * space) / 3) # shuffle, mute and loop: three small buttons of one size
        small = x + (ww - (3 * sw + 2 * space)) / 2
        for i, button in enumerate((self.shuffleButton, self.muteButton, self.loopButton)):
            button.place(small + i * (sw + space), y + 4, sw, 30 - 2 * t)
        y += bh + 28 - 18 * t
        self.volumeLabel.place(x, y + 11)
        self.volume.place(x + 64, y, ww - 64)

    def placePlayer2(self, px, top, pw):
        """The second player: the first one's narrow layout, with its ✕ in the top right corner"""
        self.player2Box = (px, top, pw)
        pad = 22
        x, ww, y = px + pad, pw - 2 * pad, top + pad
        self.closeButton2.place(px + pw - 12 - 28, top + 10, 28, 24)
        if self.art2Photos:
            self.canvas.coords(self.art2Item, x + ww - self.ART_COMPACT, y + self.ART_COMPACT_DROP)
        else:
            self.canvas.coords(self.art2Item, -9999, -9999)
        self.placeTitle2()
        y += 74
        self.elapsed2.place(x, y + 11)
        self.total2.place(x + ww, y + 11)
        self.seekBar2.place(x + 40, y, ww - 80)
        y += 38
        space = 6
        bw, bh = min(104, (ww - 2 * space) / 3), 34
        start = x + (ww - (3 * bw + 2 * space)) / 2
        for i, button in enumerate((self.prevButton2, self.playButton2, self.nextButton2)):
            button.place(start + i * (bw + space), y, bw, bh)
        y += bh + 2
        sw = min(96, (ww - 2 * space) / 3)
        small = x + (ww - (3 * sw + 2 * space)) / 2
        for i, button in enumerate((self.shuffleButton2, self.muteButton2, self.loopButton2)):
            button.place(small + i * (sw + space), y + 4, sw, 28)
        y += bh + 10
        self.volumeLabel2.place(x, y + 11)
        self.volume2.place(x + 64, y, ww - 64)

    def placeTitle2(self):
        """Channel two's song name, centred above its progress bar like the first player's and cut short the same way"""
        px, top, pw = self.player2Box
        pad = 22
        x, ww, y = px + pad, pw - 2 * pad, top + pad
        width = max(ww - (self.ART_COMPACT + 14 if self.art2Photos else 0) - (22 if not self.art2Photos else 0), 40)
        lines = max(1, int((top + pad + 78 - y) // self.title2Font.metrics("linespace"))) # the lines above its progress bar
        text = fitLines(self.title2Font, self.title2Text, width - 2, lines)
        self.title2.configure(text=text)
        if self.title2Font.measure(text) <= width:
            y = (top + y + 78 - self.title2Font.metrics("linespace")) / 2
        self.title2.place(x, y, width)

    def setCompact(self, on):
        """The first player's narrow look (two players side by side) or its usual one: symbols or words on its buttons,
        a smaller song name and cover"""
        self.compact = on
        for button, word, symbol in ((self.prevButton, "Prev", "⏴⏴"), (self.nextButton, "Next", "⏵⏵")):
            button.configure(text=symbol if on else word)
        for button in (self.prevButton, self.playButton, self.nextButton):
            self.canvas.itemconfigure(button.caption, font=(SYMBOL_FONT, 12, "bold") if on else (FONT, 10, "bold"))
        self.showPlayButton()
        self.showShuffle()
        self.showLoop()
        size = 13 if on else 18
        self.canvas.itemconfigure(self.nowPlaying.item, font=(FONT, size, "bold"))
        self.titleFont.configure(size=size)
        self.canvas.itemconfigure(self.artItem, image=self.artPhotos[2 if on else 0] if self.artPhotos else "")

    def setDual(self, on):
        """Opens the second player (a song was started on channel two) or closes it (its ✕), everywhere it shows"""
        if on == self.dual:
            return
        self.dual = on
        if on:
            self.setCompact(True)
        else:
            self.player2.stop()
            self.reset2()
        self.canvas.itemconfigure("deck2", state="hidden") # shown again once the panels have stopped moving
        self.dirtyTabs.add("chill")
        if self.currentTab == "chill" and not self.mini:
            self.layoutTab("chill")
        if self.mini:
            self.resizeMini()
        self.applyTabVisibility()
        self.updateVisBox() # the second set of bars comes or goes
        self.animateDual()

    def closeDual(self):
        self.setDual(False)

    def animateDual(self):
        """Moves the library page's panels to the other layout. Only drawn while that page is in view; anywhere else
        it simply ends up there"""
        if self.dualJob:
            self.root.after_cancel(self.dualJob)
            self.dualJob = None
        target, origin, started = (1.0 if self.dual else 0.0), self.dualT, time.perf_counter()
        if not (self.currentTab == "library" and not self.mini and self.libGeometry and not self.libOpen
                and self.root.state() != "iconic" and "library" not in self.dirtyTabs):
            self.dualT = target
            self.dirtyTabs.add("library") # laid out at the new size when it is next shown
            self.finishDual()
            return

        def step():
            self.dualJob = None
            done = min((time.perf_counter() - started) * 1000 / self.DUAL_MS, 1.0)
            eased = done * done * (3 - 2 * done) # slow at both ends
            self.dualT = origin + (target - origin) * eased
            self.placePlayers()
            if done < 1:
                self.dualJob = self.root.after(15, step)
            else:
                self.finishDual()
        step()

    def finishDual(self):
        if not self.dual:
            self.setCompact(False) # the words come back once the first player has its whole width again
        if self.libGeometry and self.currentTab == "library" and "library" not in self.dirtyTabs:
            self.placePlayers()
        self.applyTabVisibility()

    # ---- channel two: what its player shows, everywhere it shows --------------------------------------------------
    def setLyrics(self, channel, path):
        """A song started (or stopped) on this channel: its .lrc file's lyrics, wherever they show"""
        self.lyrics[channel] = loadLyrics(path) if path else None
        self.lyricClock[channel] = (0.0, time.time())
        self.libLyrics[channel].setLines(self.lyrics[channel])
        self.chillStrips[channel].setLines(self.lyrics[channel])
        if self.lyricsOpen == channel:
            if self.lyrics[channel]:
                self.fillLyricsList()
            else:
                self.closeLyrics()
        if self.playerArea and self.dualJob is None:
            self.placePlayers() # the strip comes or goes, and the voice row moves for it
        self.placeChill()
        self.placeChill2()

    def lyricPosition(self, channel):
        """Where the channel's song is now. Positions come in a few times a second, so in between it counts on"""
        position, when = self.lyricClock[channel]
        loaded, player = self.loadedPlayers()[channel - 1]
        if loaded and not player.paused:
            position += min(time.time() - when, 1.0)
        return position

    def followLyrics(self):
        """Every 100 ms: each channel's lyrics move on to the line being sung (only where they can be seen)"""
        for channel in (1, 2):
            if not self.lyrics[channel]:
                continue
            position = self.lyricPosition(channel)
            if self.currentTab == "library" and not self.mini:
                self.libLyrics[channel].follow(position)
            if self.currentTab == "chill" and not self.mini and self.chillLyricsOn[channel]:
                self.chillStrips[channel].follow(position)
            if self.lyricsOpen == channel and self.currentTab == "library":
                self.followLyricsList(position)

    def openLyrics(self, channel):
        """⤢: all of the song's lyrics over the player area, the line being sung marked"""
        self.lyricsOpen = channel
        self.fillLyricsList()
        self.placeLyricsView()
        self.applyTabVisibility()
        self.canvas.tag_raise("lyricsview")

    def closeLyrics(self):
        self.lyricsOpen = 0
        self.applyTabVisibility()

    def fillLyricsList(self):
        lst = self.lyricsList
        lst.delete(0, "end")
        for _, text in self.lyrics[self.lyricsOpen] or []:
            lst.insert("end", text or "♪")
        lst.top, lst.selected = 0, None
        name = self.titleText if self.lyricsOpen == 1 else self.title2Text
        self.lyricsTitle.configure(text=f"LYRICS  ·  {name}" + ("  ·  player 2" if self.lyricsOpen == 2 else ""))
        self.lyricsLine, self.lyricsScrolled = None, 0.0

    def placeLyricsView(self):
        if not self.lyricsOpen or not self.playerArea:
            return
        rightX, rightW, top, contentH, _ = self.playerArea
        self.lyricsPhoto = frostedImage(self.bgBlur, rightX, top, rightW, contentH, 20, 235)
        self.canvas.itemconfigure(self.lyricsPanel, image=self.lyricsPhoto)
        self.canvas.coords(self.lyricsPanel, rightX, top)
        self.lyricsTitle.place(rightX + 24, top + 24, rightW - 90)
        self.lyricsClose.place(rightX + rightW - 12 - 28, top + 12, 28, 24)
        self.lyricsList.place(rightX + 14, top + 46, rightW - 28, contentH - 60)

    def followLyricsList(self, position):
        """Marks the line being sung, and keeps it in the middle of the list unless it was just scrolled by hand"""
        times = [t for t, _ in self.lyrics[self.lyricsOpen]]
        if times[0] is None:
            return
        index = bisect.bisect_right(times, position + 0.1) - 1
        if index == self.lyricsLine or index < 0:
            return
        self.lyricsLine = index
        lst = self.lyricsList
        lst.selected, lst.marked = index, set()
        if time.time() - self.lyricsScrolled > 4:
            lst.top = min(max(index - lst.rows // 2, 0), max(len(lst.items) - lst.rows, 0))
        lst.queueDraw()

    def seekToLyric(self):
        """Double-click (or Enter) on a line: the song goes to it"""
        lines, index = self.lyrics[self.lyricsOpen], self.lyricsList.selected
        if lines and index is not None and lines[index][0] is not None:
            self.players[self.lyricsOpen - 1].seek(lines[index][0])
            self.lyricClock[self.lyricsOpen] = (lines[index][0], time.time())

    def toggleChillLyrics(self, channel):
        self.chillLyricsOn[channel] = not self.chillLyricsOn[channel]
        if self.chillLyricsOn[channel]:
            self.chillStrips[channel].setLines(self.lyrics[channel]) # straight to the line being sung
            self.chillStrips[channel].follow(self.lyricPosition(channel))
        self.placeChill() if channel == 1 else self.placeChill2()

    CHILL_LYRICS_H = 112 # the lyrics above a Chill player (their bigger letters need taller lines than the library's)

    def placeChillLyrics(self, channel, box, right, buttonY):
        """The L button at the right end of a Chill panel's button row (when its song has lyrics), and with it on, the
        lyrics playing straight on the picture just above the player"""
        x, y, width, height = box
        button, strip = self.chillLyricsButtons[channel], self.chillStrips[channel]
        if not self.lyrics[channel]:
            button.place(-9999, -9999, 30, 30)
        else:
            button.place(right - 30, buttonY, 30, 30)
            button.configure(style="Accent.TButton" if self.chillLyricsOn[channel] else "TButton")
        if self.lyrics[channel] and self.chillLyricsOn[channel]:
            top = y - 8 - self.CHILL_LYRICS_H
            if self.bgBlur is not None: # lines sliding out fade into the picture's own colour there, not to a dark smudge
                below = self.bgBlur.crop((int(x), int(top), int(x + width), int(top + self.CHILL_LYRICS_H)))
                strip.faded = below.resize((1, 1), Image.BOX).getpixel((0, 0))[:3]
                strip.texts = {} # drawn again with it
            strip.place(x + 16, top, width - 32, self.CHILL_LYRICS_H)
        else:
            strip.place(-9999, -9999, 0, 0)

    def placeChillVolume(self, channel, start, right, buttonY):
        """A Chill player's volume bar: between the end of its three buttons and the panel's right edge (or its L
        button). Out of sight if a narrow window leaves too little room for it"""
        end = right - (30 + 10 if self.lyrics[channel] else 0)
        width = min(end - (start + 16), 150)
        slider = self.chillVolumes[channel]
        if width < 50:
            slider.place(-9999, -9999, 50)
        else:
            slider.place(end - width, buttonY + 4, width)

    def setVolume(self, channel, value):
        """A volume bar moved: that channel's player, and its other bars (Library page, Chill tab, mini mode) to match"""
        self.players[channel - 1].setVolume(value)
        for slider in ((self.volume, self.chillVolumes[1], self.miniVolumes[1]) if channel == 1 else
                       (self.volume2, self.chillVolumes[2], self.miniVolumes[2])):
            if slider.value != float(value):
                slider.set(value)

    def tagAll(self, tag, *controls):
        """Adds a tag to every canvas item of these controls, so they can be shown or hidden together"""
        for control in controls:
            if isinstance(control, GlassButton):
                self.canvas.addtag_withtag(tag, f"button{id(control)}")
            elif isinstance(control, GlassSlider):
                self.canvas.addtag_withtag(tag, f"slider{id(control)}")
            elif isinstance(control, GlassLabel):
                self.canvas.addtag_withtag(tag, control.item)
            else:
                self.canvas.addtag_withtag(tag, control)

    def startChannel2(self, items, start=None):
        self.player2.play(items, start)
        self.setDual(True)

    def playSelected2(self):
        sel = self.listbox.curselection()
        if sel:
            self.startChannel2(self.songs, sel[0])

    def playSelectedTrack2(self):
        playlist, sel = self.selectedPlaylist(), self.trackList.curselection()
        if playlist and sel:
            self.startChannel2(self.playlistView(playlist), sel[0])

    def playSelectedStation2(self):
        sel = self.stationList.curselection()
        if sel:
            self.playStation(self.stations[sel[0]], channel=2)

    def onState2(self, state, text):
        """What channel two's player reported (the same reports as the first's)"""
        if state == "progress":
            self.showProgress2(*text)
        elif state == "vis":
            self.queueVis(2, text)
        elif state == "paused":
            if self.active2:
                self.syncPlayer2()
        elif state == "playing":
            label, path = text
            self.active2, self.nowTrack2 = True, (label, path)
            self.setLyrics(2, path)
            self.setTitle2(label)
            self.showArt2(path)
            self.showProgress2(0, 0, reset=True)
            self.syncPlayer2()
        elif state == "idle":
            self.reset2()
        elif state != "button": # (it isn't in Windows' media controls, so no presses come from there)
            self.logFlash(f"Player 2: {text}")

    def reset2(self):
        self.active2, self.nowTrack2 = False, None
        self.setLyrics(2, None)
        self.clearVis(2)
        self.setTitle2(T("Nothing playing"))
        self.showArt2(None)
        self.showProgress2(0, 0, reset=True)
        self.syncPlayer2()

    def setTitle2(self, text):
        self.title2Text = text
        self.placeTitle2()
        self.chill2Shown = self.mini2Shown = None
        self.syncChill2()
        self.syncMini2()

    def showArt2(self, path):
        key = os.path.normcase(str(path)) if path else None
        if key == self.art2Path:
            return
        self.art2Path = key
        data = readArt(path) if path else None
        try:
            self.art2Photos = (artImage(data, self.ART_COMPACT, 8), artImage(data, self.ART_SMALL, 10)) if data else None
        except Exception:
            self.art2Photos = None
        self.canvas.itemconfigure(self.art2Item, image=self.art2Photos[0] if self.art2Photos else "")
        self.canvas.itemconfigure(self.chill2ArtItem, image=self.art2Photos[1] if self.art2Photos else "")
        self.canvas.itemconfigure(self.mini2ArtItem, image=self.art2Photos[1] if self.art2Photos else "")
        if self.dual and self.dualT >= 1 and self.player2Box[2]:
            self.placePlayer2(*self.player2Box)
        self.placeChill2()
        if self.mini:
            self.placeMini()

    def showProgress2(self, pos, dur, reset=False):
        self.lyricClock[2] = (pos, time.time())
        if self.seeking2 and not reset:
            return
        self.seeking2 = False
        for bar in (self.seekBar2, self.chill2Seek):
            bar.configure(to=max(dur, 1))
            bar.set(pos)
        self.elapsed2.configure(text=self.formatTime(pos))
        self.total2.configure(text=self.formatTime(dur) if dur else ("" if reset else "LIVE"))

    def onSeekRelease2(self, slider=None):
        self.seeking2 = False
        self.player2.seek((slider or self.seekBar2).get())

    def onPlayButton2(self):
        """Pauses or resumes channel two; with nothing on it, plays the library's selected song there"""
        if self.active2:
            self.player2.togglePause()
        else:
            self.playSelected2()

    def syncPlayer2(self):
        """Channel two's play / pause and mute buttons, in the library, on the Chill tab and in mini mode"""
        symbol = "❚❚" if self.active2 and not self.player2.paused else "⏵"
        for button in (self.playButton2, self.chill2Buttons["play"], self.mini2Buttons["play"]):
            button.configure(text=symbol)
        muted = self.player2.muted
        self.muteButton2.configure(text="Unmute" if muted else "Mute", style="Accent.TButton" if muted else "TButton")
        self.chill2Shown = self.mini2Shown = None
        self.syncChill2()
        self.syncMini2()

    def toggleMute2(self):
        self.player2.setMuted(not self.player2.muted)
        self.syncPlayer2()

    def toggleShuffle2(self):
        self.player2.setShuffle(not self.player2.shuffle)
        self.showShuffle2()

    def showShuffle2(self):
        self.shuffleButton2.configure(style="Accent.TButton" if self.player2.shuffle else "TButton")

    def cycleLoop2(self):
        modes = list(LOOP_MODES)
        self.player2.loop = modes[(modes.index(self.player2.loop) + 1) % len(modes)]
        self.showLoop2()

    def showLoop2(self):
        self.loopButton2.configure(text=COMPACT_LOOP_MODES[self.player2.loop],
                                   style="TButton" if self.player2.loop == "off" else "Accent.TButton")

    def updateLibraryLabel(self):
        if self.dropping:
            self.libraryLabel.configure(text="DROP TO ADD TO LIBRARY", foreground=ACCENT)
        elif len(self.listbox.indices()) > 1:
            self.libraryLabel.configure(text=f"{len(self.listbox.indices())} songs selected  ·  right-click for options", foreground=ACCENT)
        elif self.search.text():
            self.libraryLabel.configure(text=f"{len(self.songs)} of {len(self.allSongs)} songs match", foreground=ACCENT)
        else:
            self.libraryLabel.configure(text=self.LIBRARY_HINT, foreground=MUTED)

    def toggleLibrary(self):
        self.libOpen = not self.libOpen
        self.placeLibrary()

    def onDropEnter(self, event):
        self.dropping = True
        self.updateLibraryLabel()

    def onDropLeave(self, event):
        self.dropping = False
        self.updateLibraryLabel()

    # ---- library -------------------------------------------------------------------------------------------------
    def logLine(self, text):
        self.log.add(text)

    def refreshSongs(self):
        """Re-reads the library (User_Music plus the stored paths) and redraws the list"""
        self.existsCache.clear() # files may have been moved since
        self.allSongs = getAllSongs([p for p in self.libraryPaths if not isYouTube(p)])
        if self.settings["youtube"]: # switched off, they stay stored but out of sight
            self.allSongs += [self.songOf(p) for p in self.libraryPaths if isYouTube(p)]
        self.addedRank = self.addedOrder()
        self.applySort()
        self.voiceRebuild = True
        if not self.allSongs:
            self.logLine(f"No songs yet. Drop music files onto the window, or put them in {songFolderPath}")
        self.loadTagsInBackground()

    def addedOrder(self):
        """Where each song comes in the library's Added order: the User_Music songs first, oldest file first, then the
        songs dropped in or added from YouTube, in the order they came"""
        folder = []
        if songFolderPath.is_dir():
            for f in songFolderPath.iterdir():
                if f.suffix.lower() in SONG_SUFFIXES:
                    try:
                        folder.append((f.stat().st_ctime, os.path.normcase(str(f)))) # on Windows: when it was put there
                    except OSError:
                        pass
        keys = [key for _, key in sorted(folder)] + [os.path.normcase(p) for p in self.libraryPaths]
        return {key: i for i, key in enumerate(dict.fromkeys(keys))}

    def songOf(self, path):
        """(name, path) of a stored song: a file's name, or a YouTube song's title behind the [YOUTUBE] tag"""
        if isYouTube(path):
            title = self.tagCache.get(os.path.normcase(str(path)), {}).get("title")
            return YT_TAG + (title or youTubeId(path)), str(path)
        return Path(path).stem, Path(path)

    def tagsOf(self, path):
        tags = self.tagCache.get(os.path.normcase(str(path)), {})
        return tags.get("artist", ""), tags.get("album", ""), tags.get("track", 0)

    @staticmethod
    def trackFromName(name):
        """A track number written at the front of the file name ("07 Messiah"), for songs whose tags don't have one"""
        match = re.match(r"(\d{1,3})(?=[\s._-])", name)
        return int(match.group(1)) if match else 0

    def sortedSongs(self, songs, mode, reverse):
        """songs ordered by a sort button. Songs are grouped by the button's field (name, number, album or artist) and
        the groups are ordered; reverse flips the groups only. Inside an album the songs always follow their track
        numbers, so an album never plays backwards. Songs missing the field come last, by name (a track number means
        nothing without an album). A playlist's Added button ("") keeps the order songs were added, newest first reversed"""
        if mode not in dict(SORT_MODES):
            return list(reversed(songs)) if reverse else list(songs)
        keyed = []
        for song in songs:
            name, path = song
            artist, album, track = self.tagsOf(path)
            name, artist, album = plainName(name).lower(), artist.lower(), album.lower() # YouTube songs by their title
            inAlbum = (track or self.trackFromName(name) or 99999, name) # numbered songs first, in order, then the rest by name
            if mode == "name":
                group, within = (name,), ()
            elif mode == "number":
                group, within = ((track,) if track else None), (name,)
            elif mode == "album": # one group per album: same-named albums in different folders stay apart
                group, within = self.albumGroup(path), ("" if album else str(Path(path).parent).lower(),) + inAlbum
            else: # artist, then each artist's albums, then each album's tracks
                group, within = ((artist,) if artist else None), ((album == "", album) + inAlbum if album else (True, "", 100000, name))
            keyed.append((group, within, song))
        keyed.sort(key=lambda k: k[1]) # inside each group first; the sort below keeps that order for equal groups, even reversed
        have = sorted((k for k in keyed if k[0] is not None), key=lambda k: k[0], reverse=reverse)
        return [k[2] for k in have + [k for k in keyed if k[0] is None]]

    def albumGroup(self, path):
        """Which album a song belongs to: its album name plus the folder it's in, so two albums both called "Greatest
        Hits" aren't mixed together. None when it has no album tag"""
        album = self.tagsOf(path)[1].lower()
        return (album, str(Path(path).parent).lower()) if album else None

    def albumBreaks(self, songs):
        """The rows where a new album starts (untagged songs are split by folder), for the lines between albums"""
        keys = [self.albumGroup(path) or ("", str(Path(path).parent).lower()) for _, path in songs]
        return {i for i in range(1, len(keys)) if keys[i] != keys[i - 1]}

    def fileExists(self, path):
        """Whether a song's file is there, remembered until the library is next re-read (one disk check per song, not
        one per song for every search keystroke)"""
        key = os.path.normcase(str(path))
        if key not in self.existsCache:
            self.existsCache[key] = isYouTube(path) or Path(path).is_file()
        return self.existsCache[key]

    def rowWidthOf(self, row):
        if row not in self.rowWidthCache:
            self.rowWidthCache[row] = self.listbox.font.measure(row)
        return self.rowWidthCache[row]

    def songRow(self, name, path):
        """number · name · album · artist, leaving out the fields a song doesn't have"""
        artist, album, track = self.tagsOf(path)
        title = name if self.fileExists(path) else f"{name} (missing)"
        return "  ·  ".join(part for part in (f"{track:02d}" if track else "", title, album, artist) if part)

    def applySort(self):
        """Orders the library by the chosen button, keeping the selected song selected"""
        sel = self.listbox.curselection()
        keep = self.songs[sel[0]][1] if sel and sel[0] < len(self.songs) else None
        songs = self.allSongs
        if not self.settings["sort"]: # Added: back to the order they came in, whatever order the last button left
            last = len(self.addedRank)
            songs = sorted(songs, key=lambda song: self.addedRank.get(os.path.normcase(str(song[1])), last))
        self.allSongs = self.sortedSongs(songs, self.settings["sort"], self.settings["reverse"])
        query = self.search.text().lower()
        self.songs = [song for song in self.allSongs if not query or self.matches(song, query)]
        self.listbox.delete(0, "end")
        for name, path in self.songs:
            self.listbox.insert("end", self.songRow(name, path))
        if self.settings["sort"] == "album":
            self.listbox.breaks = self.albumBreaks(self.songs)
        self.rowWidth = max((self.rowWidthOf(row) for row in self.listbox.items), default=0)
        if self.libGeometry and "library" not in self.dirtyTabs and self.libraryWidths() != self.libWidthsShown:
            self.placeLibrary() # the open width follows the longest row; nothing to redo when it didn't change
        if keep is not None:
            for index, (_, path) in enumerate(self.songs):
                if path == keep:
                    self.listbox.selection_set(index)
                    break

    def matches(self, song, query):
        """True when the text is inside the song's name, album or artist (ignoring capitals)"""
        name, path = song
        artist, album, _ = self.tagsOf(path)
        return any(query in field.lower() for field in (name, album, artist))

    def onSearchChange(self):
        self.applySort()
        self.updateLibraryLabel()

    def setSort(self, mode):
        if mode == self.settings["sort"]:
            self.settings["reverse"] = not self.settings["reverse"] # pressing the active one flips the order
        else:
            self.settings["sort"], self.settings["reverse"] = mode, False
        self.showSortButtons()
        self.applySort()
        self.persistSettings()

    def showSortButtons(self):
        for mode, button in self.sortButtons.items():
            on = mode == self.settings["sort"]
            arrow = " ▼" if on and self.settings["reverse"] else " ▲" if on else ""
            button.configure(text=T(dict(LIST_SORT_MODES)[mode]) + arrow, style="Accent.TButton" if on else "TButton")

    def loadTagsInBackground(self):
        """Reads tags of songs that aren't cached yet (or changed) off the main thread, then re-sorts"""
        todo = []
        paths = [path for _, path in self.allSongs] + [Path(t) for pl in self.playlists for t in pl["tracks"] if not isYouTube(t)]
        for path in dict.fromkeys(p for p in paths if not isYouTube(p)): # a YouTube song's details come from YouTube
            try:
                modified = path.stat().st_mtime
            except OSError:
                continue
            cached = self.tagCache.get(os.path.normcase(str(path)))
            if not cached or cached.get("m") != modified:
                todo.append((path, modified))
        if todo:
            threading.Thread(target=self.readAllTags, args=(todo,), daemon=True).start()

    def readAllTags(self, todo):
        found = {}
        for path, modified in todo:
            artist, album, track = readTags(path)
            found[os.path.normcase(str(path))] = {"m": modified, "artist": artist, "album": album, "track": track}
        self.events.put(("tags", found))

    def addToLibrary(self, paths):
        """Remembers the songs that aren't in the library yet. Returns the ones that were new (nothing is saved here)"""
        known = {os.path.normcase(str(path)) for _, path in self.allSongs}
        known |= {os.path.normcase(p) for p in self.libraryPaths}
        fresh = []
        for path in paths:
            full = str(Path(path).resolve())
            if os.path.normcase(full) not in known:
                known.add(os.path.normcase(full))
                fresh.append(full)
        self.libraryPaths += fresh
        return fresh

    def onSelectAll(self, event):
        if self.currentTab == "library":
            self.listbox.selectAll()
        elif self.currentTab == "playlists":
            self.trackList.selectAll() # the playlist's songs (playlists themselves are picked one at a time)

    def selectedSongs(self):
        """The (name, path) of every selected row in the library list"""
        return [self.songs[i] for i in self.listbox.indices() if i < len(self.songs)]

    def showSongMenu(self, event):
        """Right-click menu. It acts on every selected song, so the wording follows how many there are"""
        count = len(self.selectedSongs())
        many = count > 1
        playlists = [{"label": playlist["name"], "translate": False, "command": lambda i=index: self.addSelectedToPlaylist(i)}
                     for index, playlist in enumerate(self.playlists)]
        newPlaylist = {"label": "New playlist...", "command": lambda: self.addPlaylistDialog(self.selectedSongs())}
        self.updateLibraryLabel()
        self.songMenu.show(event.x_root, event.y_root, [
            {"label": f"Play (the first of {count})" if many else "Play", "command": self.playSelected},
            {"label": "Add to playlist", "sub": [newPlaylist] + ([None] + playlists if playlists else [])},
            self.editEntry(self.selectedSongs()),
            self.showFileEntry(),
            None,
            {"label": f"Delete {count} songs from library" if many else "Delete from library", "command": self.removeSelectedSong},
        ])

    def showFileEntry(self):
        """The menu's "Show in File Explorer" for the song right-clicked (with several selected, the one clicked last).
        A YouTube song opens on YouTube instead"""
        index = self.listbox.selected
        if index is None or index >= len(self.songs):
            return {"label": "Show in File Explorer", "disabled": True}
        path = self.songs[index][1]
        if isYouTube(path):
            return {"label": "Open on YouTube", "command": lambda: webbrowser.open(str(path))}
        if not self.fileExists(path):
            return {"label": "Show in File Explorer (the file is missing)", "disabled": True}
        return {"label": "Show in File Explorer", "command": lambda: self.showInExplorer(path)}

    def showInExplorer(self, path):
        """Opens the song's folder with the file picked out"""
        try:
            subprocess.Popen(f'explorer /select,"{Path(path)}"') # explorer wants the quotes around the path only
        except OSError as e:
            self.logFlash(f"Couldn't open File Explorer: {e}")

    def addSelectedToPlaylist(self, index):
        """Adds the selected songs to a playlist (songs already in it are skipped)"""
        playlist = self.playlists[index]
        have = {os.path.normcase(t) for t in playlist["tracks"]}
        new = [str(path) for _, path in self.selectedSongs() if os.path.normcase(str(path)) not in have]
        playlist["tracks"] += new
        self.persistPlaylists()
        if self.selectedPlaylist() is playlist:
            self.refreshPlaylistTracks()
        skipped = len(self.selectedSongs()) - len(new)
        note = f" ({skipped} already in it)" if skipped else ""
        message = f"Added {len(new)} song{'s' if len(new) != 1 else ''} to {playlist['name']}{note}."
        self.setPlaylistStatus(message, "ok")
        self.logFlash(message)

    def removeSelectedSong(self):
        """Forgets the selected songs. Files are never deleted, and playlists keep their copy of each song"""
        songs = self.selectedSongs()
        if not songs:
            return
        # songs in User_Music are found by scanning that folder, so only the dropped-in ones can be forgotten
        stored = {os.path.normcase(p) for p in self.libraryPaths}
        removable = [(name, path) for name, path in songs if os.path.normcase(str(path)) in stored]
        if not removable:
            self.logFlash(f"{songs[0][0]} is in the User_Music folder. Delete the file there to remove it." if len(songs) == 1
                          else "Those songs are in the User_Music folder. Delete the files there to remove them.")
            return
        if len(removable) > 1 and not self.confirmDialog(
                f"Remove {len(removable)} songs from the library? Your music files are not touched, and playlists keep them.", "Remove"):
            return
        gone = {os.path.normcase(str(path)) for _, path in removable}
        self.libraryPaths = [p for p in self.libraryPaths if os.path.normcase(p) not in gone]
        self.persistLibrary()
        self.refreshSongs()
        what = removable[0][0] if len(removable) == 1 else f"{len(removable)} songs"
        left = f" {len(songs) - len(removable)} in User_Music stayed." if len(removable) < len(songs) else ""
        self.logFlash(f"Removed {what} from the library (the files themselves are untouched).{left}")

    def persistLibrary(self):
        problem = saveLibrary(self.libraryPaths)
        if problem:
            self.logFlash(problem)

    # ---- editing a song's details: written into the file's tags, and the file renamed to the song's name ----------
    RESERVED_NAMES = {"CON", "PRN", "AUX", "NUL", *(f"COM{i}" for i in range(1, 10)), *(f"LPT{i}" for i in range(1, 10))}

    def editEntry(self, songs):
        """The song menus' Edit page: the songs' details and their album art, each greyed out with the reason when it
        can't be done (editing changes the file, so only some songs can be edited)"""
        details, art = self.cantEdit(songs), self.cantEditArt(songs)
        return {"label": "Edit", "sub": [
            {"label": details, "disabled": True} if details else {"label": "Details...", "command": lambda: self.editSongDialog(songs)},
            {"label": art, "disabled": True} if art else {"label": "Album art...", "command": lambda: self.editArtDialog(songs)}]}

    def cantEdit(self, songs):
        """Why these songs' details can't be edited (shown greyed out in the menu), or None when they all can"""
        if not songs:
            return "Details..."
        for _, path in songs:
            if isYouTube(path):
                return "Details (not for YouTube songs)"
            if not self.fileExists(path):
                return "Details (a file is missing)" if len(songs) > 1 else "Details (the file is missing)"
            if Path(path).suffix.lower() not in TAG_WRITABLE:
                return f"Details (not possible for {Path(path).suffix} files)"
        return None

    def editSongDialog(self, songs):
        """Edits the songs' details. One song: its number, name (which renames the file), album and artist.
        Several: the same fields for all of them (a shared name is NOT RECOMMENDED: see plannedNames). A field they share
        starts filled in, one where they differ starts blank, and only the fields that are changed are written, after
        an are-you-sure"""
        if self.cantEdit(songs):
            return
        paths = [Path(path) for _, path in songs]
        many = len(paths) > 1
        details = [readTags(path) for path in paths] # straight from the files, in case they changed since they were cached
        shared = [details[0][i] if all(d[i] == details[0][i] for d in details) else None for i in range(3)] # None: they differ
        artist, album, track = shared
        start = {"number": str(track) if track else "", "album": album or "", "artist": artist or ""}
        various = "  ·  various: left as they are unless you type one"
        suffix = paths[0].suffix
        sharedName = paths[0].stem if all(p.stem == paths[0].stem for p in paths) else ""
        sharedType = suffix if all(p.suffix.lower() == suffix.lower() for p in paths) else None # None: a mix of types

        dialog = GlassDialog(self, "Edit song details", 480, 400)
        dialog.label(f"EDIT {len(paths)} SONGS" if many else "EDIT SONG DETAILS", 28, 24, 12, True, TEXT)
        dialog.label("NUMBER", 28, 62)
        numberEntry = dialog.field(28, 80, 80)
        if many:
            dialog.label("SONG  (also the file names)" + ("" if sharedName else "  ·  various"), 120, 62)
            nameEntry = dialog.field(120, 80, 200)
            nameEntry.insert(0, sharedName)
            dialog.label("NOT RECOMMENDED", 330, 99, 9, True, "#ff7b7b") # every song would end up with the same name
        else:
            dialog.label("SONG  (also the file's name)", 120, 62)
            nameEntry = dialog.field(120, 80, 282)
            nameEntry.insert(0, paths[0].stem)
            dialog.label(suffix, 410, 99, 11, False, MUTED) # the type stays: it is shown, never typed
        dialog.label("ALBUM" + (various if album is None else ""), 28, 132)
        albumEntry = dialog.field(28, 150, 424)
        dialog.label("ARTIST" + (various if artist is None else ""), 28, 202)
        artistEntry = dialog.field(28, 220, 424)
        note = ("Saved into each file itself. Only the fields you change are written." if many
                else "Saved into the file itself, and the file is renamed to the song's name.")
        dialog.label(note, 28, 272, 9, False, MUTED, 424)
        problem = dialog.label("", 28, 294, 9, False, "#ff7b7b", 424)
        numberEntry.insert(0, start["number"])
        albumEntry.insert(0, start["album"])
        artistEntry.insert(0, start["artist"])

        def submit(event=None):
            number = numberEntry.get().strip()
            if number and not (number.isdigit() and 0 < int(number) < 1000):
                problem.configure(text="The number must be a whole number from 1 to 999, or blank.")
                return "break"
            if many:
                error = confirmMany(number)
                if error is False:
                    return "break" # nothing changed, or they said no
            else:
                name, error = self.checkSongName(nameEntry.get(), suffix)
                if not error:
                    error = self.saveSongDetails(paths[0], name, int(number or 0), albumEntry.get().strip(), artistEntry.get().strip())
            if error:
                problem.configure(text=error)
            else:
                dialog.close()
            return "break"

        def confirmMany(number):
            """Asks before changing several files. Returns what went wrong, None when saved, False when nothing was"""
            changes, lines = {}, []
            typed = nameEntry.get().strip()
            if typed and typed != sharedName: # blank leaves each song its own name
                name, error = self.checkSongName(typed, sharedType)
                if error:
                    return error
                changes["name"] = name
                lines.append(f'Name: "{name}"  (NOT RECOMMENDED: in one folder they become "{name}", "{name} (2)"...)')
            for key, field, label in (("track", number, "Number"), ("album", albumEntry.get().strip(), "Album"),
                                      ("artist", artistEntry.get().strip(), "Artist")):
                if field != start["number" if key == "track" else key]:
                    changes[key] = int(field or 0) if key == "track" else field
                    lines.append(f'{label}: "{field}"' if field else f"{label}: removed")
            if not changes:
                dialog.close()
                return False
            count = "both" if len(paths) == 2 else f"all {len(paths)}"
            message = f"This will change multiple songs' data!\n\n{'   ·   '.join(lines)}\nfor {count} songs."
            if not self.confirmDialog(message, "Change"):
                dialog.win.grab_set() # back to the edit window, which lost its hold to the question
                return False
            return self.saveManySongs(paths, changes)

        dialog.button("Save", 480 - 28 - 110, 400 - 62, 110, submit, "accent")
        dialog.button("Cancel", 480 - 28 - 110 - 8 - 90, 400 - 62, 90, dialog.close)
        dialog.onReturn(submit)
        dialog.show(albumEntry if many else nameEntry)

    def checkSongName(self, name, suffix):
        """(the name to use, None), or (None, why it can't be a file name). The file type can't be changed: suffix is
        the songs' type, None for songs of several types"""
        name = name.strip().rstrip(" .") # Windows drops trailing dots and spaces
        stem, dot, typed = name.rpartition(".")
        if dot and "." + typed.lower() in TAG_WRITABLE | SONG_SUFFIXES: # a file type typed on the end
            if not suffix:
                return None, "The file types can't be changed. Leave the type off the name."
            if "." + typed.lower() != suffix.lower():
                return None, f"The file type can't be changed. It stays {suffix}."
            name = stem.rstrip(" .") # the same type: just drop it
        if not name:
            return None, "The song needs a name."
        if re.search(r'[<>:"/\\|?*\x00-\x1f]', name):
            return None, 'A file name can\'t contain any of  < > : " / \\ | ? *'
        if name.split(".")[0].upper() in self.RESERVED_NAMES:
            return None, "Windows keeps that name for itself. Pick another."
        if len(name) > 200:
            return None, "That name is too long for a file name."
        return name, None

    def changeSongFile(self, path, name, track, album, artist, title=None):
        """Writes one song's details into its file (None: leave that one as it is) and, given a name, renames the file
        to it, pointing the library, the playlists and the tag cache at the new name (saved by finishSongEdits). The
        title written is the name, unless a title is given. Returns (where the file is now, None when nothing was
        written; what went wrong or None)"""
        newPath = path.with_name(name + path.suffix) if name else path
        same = os.path.normcase(str(newPath)) == os.path.normcase(str(path)) # at most the capitals change
        if self.nowTrack and os.path.normcase(str(self.nowTrack[1])) == os.path.normcase(str(path)):
            return None, "That song is playing. Stop it first: Windows won't let a file in use be changed."
        if not same and newPath.exists():
            return None, f"There's already a file called {newPath.name} in that folder."
        try:
            writeTags(path, title or name, artist, album, track)
        except PermissionError:
            return None, "Couldn't change the file: it's read-only, or another program has it open."
        except Exception as e:
            return None, f"Couldn't write the details into the file: {e}"
        problem = None
        if newPath.name != path.name:
            try:
                os.rename(path, newPath)
            except OSError as e:
                problem = f"The details were saved, but the file couldn't be renamed: {e.strerror or e}"
                newPath = path
        if newPath != path:
            old, new = os.path.normcase(str(path)), str(newPath)
            self.libraryPaths = [new if os.path.normcase(p) == old else p for p in self.libraryPaths]
            for playlist in self.playlists:
                playlist["tracks"] = [new if os.path.normcase(t) == old else t for t in playlist["tracks"]]
            self.tagCache.pop(old, None)
        try:
            modified = newPath.stat().st_mtime
        except OSError:
            modified = 0
        artist, album, track = readTags(newPath) # what it holds now, the fields left alone included
        self.tagCache[os.path.normcase(str(newPath))] = {"m": modified, "artist": artist, "album": album, "track": track}
        return newPath, problem

    def plannedNames(self, paths, name):
        """The file name (without its type) each song gets when several are given one name. Two files in one folder
        can't share a name, so as Windows does, the next gets "name (2)", then "name (3)"... A song keeps its own file
        name when it is already the one it would get"""
        planned, taken = {}, set()
        for path in paths:
            number = 1
            while True:
                stem = name if number == 1 else f"{name} ({number})"
                target = path.with_name(stem + path.suffix)
                key = os.path.normcase(str(target))
                if key not in taken and (key == os.path.normcase(str(path)) or not target.exists()):
                    break
                number += 1
            taken.add(key)
            planned[path] = stem
        return planned

    def finishSongEdits(self, paths):
        """After files were changed: saves the library, playlists and tag cache, redraws, and keeps them selected"""
        self.persistLibrary()
        self.persistPlaylists()
        saveTagCache(self.tagCache)
        self.refreshSongs()
        self.refreshPlaylistTracks()
        keys = {os.path.normcase(str(path)) for path in paths}
        picked = {i for i, (_, songPath) in enumerate(self.songs) if os.path.normcase(str(songPath)) in keys}
        if len(picked) == 1:
            self.listbox.select(min(picked)) # wherever its new name sorts it
        elif picked:
            self.listbox.setChosen(picked, min(picked))
            self.listbox.see(min(picked))

    def saveSongDetails(self, path, name, track, album, artist):
        """One song: its details, and its file renamed to its name. Returns what went wrong, or None when it's done"""
        newPath, problem = self.changeSongFile(path, name, track, album, artist)
        if newPath:
            self.finishSongEdits([newPath])
            if not problem:
                self.logFlash(f"Saved the details of {name}.")
        return problem

    def saveManySongs(self, paths, changes):
        """Several songs: the changed fields ("name", "track", "album", "artist") written into each. Every song that can
        be is changed even when some can't. Returns what went wrong, or None when all were saved"""
        done, failed = [], []
        names = self.plannedNames(paths, changes["name"]) if "name" in changes else {}
        for path in paths:
            newPath, problem = self.changeSongFile(path, names.get(path), changes.get("track"), changes.get("album"),
                                                   changes.get("artist"), title=changes.get("name"))
            if newPath:
                done.append(newPath)
            if problem:
                failed.append(f"{path.stem}: {problem}")
        if done:
            self.finishSongEdits(done)
        if failed:
            more = f" (and {len(failed) - 2} more)" if len(failed) > 2 else ""
            return f"Changed {len(done)} of {len(paths)} songs. " + "  ".join(failed[:2]) + more
        self.logFlash(f"Saved the details of {len(done)} songs.")
        return None

    # ---- album art: written into the song file (a YouTube song's replaces its saved thumbnail) ----------------------
    def cantEditArt(self, songs):
        """Why these songs' album art can't be changed (shown greyed out in the menu), or None when it can"""
        if not songs:
            return "Album art..."
        for _, path in songs:
            if isYouTube(path):
                continue # its cover is the thumbnail kept in data, which can be swapped
            if not self.fileExists(path):
                return "Album art (a file is missing)" if len(songs) > 1 else "Album art (the file is missing)"
            if Path(path).suffix.lower() not in ART_TYPES:
                return f"Album art (not possible for {Path(path).suffix} files)"
        return None

    def editArtDialog(self, songs):
        """Shows the songs' album art (when they share one) with the size of picture to use, and changes or removes it.
        Several songs get the same picture, after an are-you-sure"""
        if self.cantEditArt(songs):
            return
        many = len(songs) > 1
        arts = [readArt(path) for _, path in songs]
        shared = arts[0] if all(art == arts[0] for art in arts) else False # False: they differ
        youTube = any(isYouTube(path) for _, path in songs)

        dialog = GlassDialog(self, "Album art", 480, 360)
        dialog.label(f"ALBUM ART  ·  {len(songs)} SONGS" if many else "ALBUM ART", 28, 24, 12, True, TEXT)
        try:
            preview = artImage(shared, 128, 12) if shared else None
        except Exception:
            preview = None # not a picture it can read
        if preview:
            dialog.photos.append(preview)
            dialog.canvas.create_image(28, 62, anchor="nw", image=preview)
        else:
            box = roundedImage(128, 128, (0, 0, 0, 70), (255, 255, 255, 50), radius=12)
            dialog.photos.append(box)
            dialog.canvas.create_image(28, 62, anchor="nw", image=box)
            GlassLabel(dialog.canvas, "Various" if shared is False else "No album art", 9, False, MUTED, anchor="center").place(92, 126)
        dialog.label("IDEAL PICTURE", 176, 62)
        dialog.label(f"A square JPG or PNG, {ART_SIZE} × {ART_SIZE} pixels (at least {ART_MIN} × {ART_MIN}).", 176, 82, 11, False, TEXT, 276)
        dialog.label(f"Other shapes are cropped to the middle square, and bigger pictures shrunk to {ART_SIZE} × {ART_SIZE}. "
                     "It is saved into the song file itself.", 176, 146, 9, False, MUTED, 276)
        if youTube:
            dialog.label("Remove gives a YouTube song its video's thumbnail back.", 28, 216, 9, False, MUTED, 424)
        problem = dialog.label("", 28, 240, 9, False, "#ff7b7b", 424)

        def choose():
            start = Path.home() / "Pictures"
            picked = filedialog.askopenfilename(parent=dialog.win, title=T("Choose album art"), filetypes=PICTURE_TYPES,
                                                initialdir=str(start if start.is_dir() else BASE_DIR))
            if not picked:
                return
            try:
                data = preparedArt(picked)
            except (OSError, ValueError, SyntaxError, Image.DecompressionBombError) as e:
                problem.configure(text=f"Couldn't open that picture ({Path(picked).name}): {e}")
                return
            apply(data)

        def apply(data):
            if many:
                message = (f"This will change the album art of {len(songs)} songs." if data
                           else f"This will remove the album art of {len(songs)} songs.")
                if not self.confirmDialog(message, "Change" if data else "Remove"):
                    dialog.win.grab_set() # back to the art window, which lost its hold to the question
                    return
            error = self.saveArt(songs, data)
            if error:
                problem.configure(text=error)
            else:
                dialog.close()

        dialog.button("Choose picture...", 480 - 28 - 150, 360 - 62, 150, choose, "accent")
        dialog.button("Remove", 480 - 28 - 150 - 8 - 100, 360 - 62, 100, lambda: apply(None))
        dialog.button("Close", 480 - 28 - 150 - 8 - 100 - 8 - 90, 360 - 62, 90, dialog.close)
        dialog.show()

    def changeArt(self, path, data):
        """Writes one song's album art (None removes it). Returns what went wrong, or None"""
        if isYouTube(path):
            cover = YT_COVERS_DIR / f"{youTubeId(path)}.jpg"
            try:
                if data:
                    YT_COVERS_DIR.mkdir(parents=True, exist_ok=True)
                    cover.write_bytes(data)
                else:
                    cover.unlink(missing_ok=True)
            except OSError as e:
                return f"Couldn't save the picture: {e.strerror or e}"
            return None
        key = os.path.normcase(str(path))
        if any(track and os.path.normcase(str(track[1])) == key for track in (self.nowTrack, self.nowTrack2)):
            return "That song is playing. Stop it first: Windows won't let a file in use be changed."
        try:
            writeArt(path, data)
        except PermissionError:
            return "Couldn't change the file: it's read-only, or another program has it open."
        except Exception as e:
            return f"Couldn't write the album art into the file: {e}"
        return None

    def saveArt(self, songs, data):
        """Writes the album art (None removes it) into each of the songs. Every song that can be is changed even when
        some can't. A YouTube song whose art was removed gets its thumbnail fetched again. Returns what went wrong, or
        None when all were done"""
        done, failed = [], []
        for name, path in songs:
            problem = self.changeArt(path, data)
            if problem:
                failed.append(f"{name}: {problem}")
            else:
                done.append((name, path))
        videos = [youTubeId(path) for _, path in done if isYouTube(path)] if data is None else []
        if videos:
            threading.Thread(target=lambda: upgradeYouTubeCovers(videos) and self.events.put(("coversUpgraded",)), daemon=True).start()
        self.refreshArt()
        if failed:
            more = f" (and {len(failed) - 2} more)" if len(failed) > 2 else ""
            return f"Changed the album art of {len(done)} of {len(songs)} songs. " + "  ".join(failed[:2]) + more
        if len(done) > 1:
            self.logFlash(f"Saved the album art of {len(done)} songs." if data else f"Removed the album art of {len(done)} songs.")
        elif data:
            self.logFlash(f"Saved the album art of {done[0][0]}.")
        elif not isYouTube(done[0][1]) and readArt(done[0][1]): # a cover.jpg / folder.jpg next to it
            self.logFlash(f"Removed the album art of {done[0][0]}. The cover picture in its folder still shows.")
        else:
            self.logFlash(f"Removed the album art of {done[0][0]}.")
        return None

    def refreshArt(self):
        """Reads the playing songs' covers again, as one of them may have changed"""
        if self.active and self.nowTrack:
            self.artPath = None
            self.showArt(self.nowTrack[1])
        if self.active2 and self.nowTrack2:
            self.art2Path = None
            self.showArt2(self.nowTrack2[1])

    def logFlash(self, text):
        self.logLine(text)
        self.showLogFor(6)

    def animateVis(self):
        """The visualizer bars follow the music: they jump up with the sound and fall back smoothly. Runs every 40 ms
        while there is something to show; once the bars have settled flat it stops until the next sound report
        (wakeVis), so an idle player does no drawing at all"""
        now = time.time()
        while self.visQueue and self.visQueue[0][0] <= now:
            _, levels, channel = self.visQueue.popleft()
            self.visTargets[channel] = levels
        for channel, last in self.visLasts.items():
            if now - last > 0.5:
                self.visTargets[channel] = [0.0] * VIS_BARS # no reports: stopped
        first, second = self.visTargets[1], self.visTargets[2]
        for i in range(VIS_BARS):
            one, two = (first[i] if i < len(first) else 0.0), (second[i] if i < len(second) else 0.0)
            # with the second player open each set shows its own channel; closed, the one set shows whatever plays
            for shown, goal in ((self.visShown, one if self.dual else max(one, two)), (self.visShown2, two if self.dual else 0.0)):
                shown[i] = goal if goal > shown[i] else max(goal, shown[i] - 0.09)
        self.drawVis()
        if self.visQueue or any(self.visShown) or any(self.visShown2) or now - max(self.visLasts.values()) <= 0.5:
            self.visJob = self.root.after(40, self.animateVis)
        else:
            self.visJob = None

    def queueVis(self, channel, levels):
        """Levels from a channel, shown when the sound they came from is actually heard (a YouTube song's levels come
        from the speakers: heard already)"""
        self.visQueue.append((time.time() + (0 if self.players[channel - 1].onYouTube else 0.22), levels, channel))
        self.visLasts[channel] = time.time()
        self.wakeVis()

    def clearVis(self, channel):
        self.visQueue = collections.deque((e for e in self.visQueue if e[2] != channel), maxlen=self.visQueue.maxlen)
        self.visTargets[channel] = [0.0] * VIS_BARS

    def wakeVis(self):
        if not self.visJob:
            self.visJob = self.root.after(40, self.animateVis)

    def drawVis(self):
        """Draws the bars where the visualizer currently lives (also used to move them while the loop sleeps)"""
        for bars, shown, (x, base, height) in ((self.visBars, self.visShown, self.visBox), (self.visBars2, self.visShown2, self.visBox2)):
            if bars is self.visBars2 and not self.dual:
                x = -9999 # no second player: its bars are out of sight
            for i, bar in enumerate(bars):
                bx = x + 2 + i * 5
                self.canvas.coords(bar, bx, base, bx, base - 1 - shown[i] * (height - 1))

    def tick(self):
        now = time.localtime()
        self.clock.configure(text=f"{formatTime(LANGUAGE, now)}  ·  {formatDate(LANGUAGE, now)}")
        if self.wantNight() != self.nightActive: # 9 PM or 7 AM went by
            self.applyBackground(fade=True)
        self.root.after(1000, self.tick)

    def pump(self):
        """Handles everything the background threads asked for: player state, tags, keys, voice. Runs every 100 ms"""
        try:
            while True:
                kind, *rest = self.events.get_nowait()
                if kind == "state":
                    state, text = rest
                    if state == "progress":
                        self.showProgress(*text)
                    elif state == "vis":
                        self.queueVis(1, text)
                    elif state == "paused":
                        if self.active: # a late event from Stop must not undo the reset
                            self.showPlayButton()
                    elif state == "playing":
                        label, path = text
                        self.active = True
                        self.setTitle(label)
                        self.showArt(path)
                        self.nowTrack = (label, path)
                        self.setLyrics(1, path)
                        self.updateWeather()
                        self.highlightPlaying(path)
                        self.showPlayButton()
                        self.showProgress(0, 0, reset=True)
                    elif state == "idle":
                        self.resetPlayback()
                    elif state == "button": # pressed in Windows' media controls: earbuds, the volume flyout
                        key = {"Play": "play", "Pause": "pause", "Next": "next", "Previous": "prev", "Stop": "stop"}.get(text)
                        if key:
                            self.onMediaKey(key, "windows")
                    else:
                        self.logFlash(text) # errors, e.g. a song missing from where it was dropped in
                        self.setPlaylistStatus(text, "error")
                elif kind == "state2":
                    self.onState2(*rest)
                elif kind == "tags":
                    self.tagCache.update(rest[0])
                    saveTagCache(self.tagCache)
                    self.applySort()
                    self.refreshPlaylistTracks()
                elif kind == "media":
                    self.onMediaKey(*rest)
                elif kind == "thumb": # a button in the taskbar preview
                    command = self.thumbBar and self.thumbBar.commands.get(rest[0])
                    if command:
                        command()
                elif kind == "thumbReady" and self.thumbBar: # the taskbar button exists, so its preview can get buttons
                    self.thumbBar.add()
                elif kind == "imported":
                    self.finishImport(rest[0])
                elif kind == "youtubeAdded":
                    self.finishYouTube(*rest)
                elif kind == "coversUpgraded": # the playing songs' covers may be among them
                    self.refreshArt()
                elif kind == "playlistStatus":
                    self.setPlaylistStatus(*rest)
                elif kind == "log":
                    self.logLine(rest[0])
                elif kind == "radioStatus":
                    self.setRadioStatus(*rest)
                elif kind == "logFlash": # problems show even though the voice log is hidden while voice is off
                    self.logFlash(rest[0])
                elif kind == "voice":
                    if not self.mentionsRadio(rest[0]): # radio commands are reported by the Radio tab instead
                        self.logLine(f'Heard: "{rest[0]}"')
                    self.handleCommand(rest[0])
                elif kind == "voiceState":
                    self.setVoiceState(rest[0])
        except queue.Empty:
            pass
        self.syncMini()
        self.syncChill()
        self.syncMini2()
        self.syncChill2()
        self.followLyrics()
        if self.thumbBar:
            self.thumbBar.setPlaying(self.anyPlaying())
        # Windows' media controls (where earbud taps arrive) see both channels as one: playing while either plays, so
        # the next tap is a pause, and paused while both are, so it's a play
        loaded = self.active or self.active2
        track = self.nowTrack if self.active else self.nowTrack2
        media = ("playing" if self.anyPlaying() else "paused") if loaded else "stopped", track[0] if loaded and track else ""
        if media != self.mediaShown: # Windows tells the earbuds, so their next press is the right one
            self.mediaShown = media
            self.player.showInWindows(*media)
        if self.navTarget is not None:
            self.placeNavRing() # the control may have moved (the library opening, a new cover)
        self.root.after(100, self.pump)

    def onDrop(self, event):
        self.dropping = False
        self.updateLibraryLabel()
        paths = [Path(p) for p in self.root.tk.splitlist(event.data)]
        threading.Thread(target=self.importFiles, args=(paths,), daemon=True).start()
        return event.action

    def importFiles(self, paths):
        """Background thread: finds the files in what was dropped (folders are searched too)"""
        found = []
        for path in paths:
            found += [f for f in path.rglob("*") if f.is_file()] if path.is_dir() else [path]
        self.events.put(("imported", found))

    def finishImport(self, found):
        """Adds dropped files to the library (back on the main thread, after importFiles searched the folders)"""
        songs, added, skipped = [], 0, 0
        for f in found:
            suffix = f.suffix.lower()
            if suffix not in DROP_SUFFIXES:
                skipped += 1
            elif suffix == ".xspf": # a playlist file is tiny, and the voice "playlist" command looks for it in User_Music
                songFolderPath.mkdir(exist_ok=True)
                try:
                    if not (songFolderPath / f.name).exists():
                        shutil.copy2(f, songFolderPath / f.name)
                        added += 1
                except OSError as e:
                    self.logLine(f"Could not copy {f.name}: {e}")
            else:
                songs.append(f)
        fresh = self.addToLibrary(songs)
        added += len(fresh)
        if len(fresh) < len(songs):
            self.logLine(f"{len(songs) - len(fresh)} of them were already in the library")
        note = f", ignored {skipped} unsupported" if skipped else ""
        self.logFlash(f"Added {added} file(s) to the library{note}. They stay where they are.")
        self.persistLibrary()
        self.refreshSongs()

    # ---- playback ------------------------------------------------------------------------------------------------
    def playSelected(self):
        sel = self.listbox.curselection()
        if sel:
            self.player.play(self.songs, sel[0]) # the rest of the library follows, so Next/Prev work

    def onSpace(self, event):
        if isinstance(event.widget, (tk.Entry, tk.Text)):
            return None # typing a space, not a play/pause toggle
        if event.widget.winfo_toplevel() is self.root: # not while a dialog is open
            self.toggleAll()
        return "break"

    def onMediaKey(self, key, source="key"):
        if key in ("playpause", "play", "pause"):
            now = time.time()
            if now - self.lastPlayPause < 0.4:
                return # one tap can arrive more than once (as a key and as "play"), and a second toggle would undo it
            self.lastPlayPause = now
            if not (self.active or self.active2): # nothing loaded: play starts the selected song
                if key != "pause":
                    self.onPlayButton()
            elif key == "playpause":
                self.toggleAll()
            else: # only resumes if paused, only pauses if playing
                self.pauseAll(key == "pause")
        elif key == "next":
            self.player.next()
        elif key == "prev":
            self.player.previous()
        elif key == "stop":
            self.stop()

    def loadedPlayers(self):
        """(loaded, player) for both channels"""
        return ((self.active, self.player), (self.active2, self.player2))

    def anyPlaying(self):
        return any(loaded and not player.paused for loaded, player in self.loadedPlayers())

    def pauseAll(self, paused):
        """Pauses every player with a song loaded, or resumes them all"""
        for loaded, player in self.loadedPlayers():
            if loaded and player.paused != paused:
                player.togglePause()

    def toggleAll(self):
        """Space, earbud taps and the media keys: if anything is playing, everything pauses; pressed again, everything
        that was paused plays on. With nothing loaded, it starts the selected song (on the first player)"""
        if not (self.active or self.active2):
            self.onPlayButton()
        else:
            self.pauseAll(self.anyPlaying())

    def onPlayButton(self):
        """Play starts the selected song when idle, otherwise it toggles pause"""
        if self.active:
            self.player.togglePause()
        else:
            if not self.listbox.curselection() and self.songs:
                self.listbox.selection_set(0)
            self.playSelected()

    def highlightPlaying(self, path):
        """Moves the selection to the song that just started, in the library and in the open playlist"""
        key = os.path.normcase(str(path))
        for lst, songs in ((self.listbox, self.songs), (self.trackList, self.playlistView(self.selectedPlaylist()) if self.selectedPlaylist() else [])):
            for index, (_, songPath) in enumerate(songs):
                if os.path.normcase(str(songPath)) == key:
                    if not lst.marked: # not while several songs are being picked
                        lst.select(index)
                    break

    def stop(self):
        self.player.stop()
        self.forcedWeather.clear() # "stop" ends the snow and rain someone asked for, too
        self.resetPlayback()

    def resetPlayback(self):
        self.active = False
        self.clearVis(1)
        self.setTitle(T("Nothing playing"))
        self.showArt(None)
        self.nowTrack = None
        self.setLyrics(1, None)
        self.updateWeather()
        self.showPlayButton()
        self.showProgress(0, 0, reset=True)

    def toggleShuffle(self):
        self.settings["shuffle"] = not self.player.shuffle
        self.player.setShuffle(self.settings["shuffle"])
        self.showShuffle()
        self.persistSettings()

    def showShuffle(self):
        on = self.player.shuffle
        text = "Shuffle" if self.compact else "Shuffle: On" if on else "Shuffle: Off" # narrow: the colour says on or off
        self.shuffleButton.configure(text=text, style="Accent.TButton" if on else "TButton")

    def cycleLoop(self):
        modes = list(LOOP_MODES)
        self.settings["loop"] = self.player.loop = modes[(modes.index(self.player.loop) + 1) % len(modes)]
        self.showLoop()
        self.persistSettings()

    def showLoop(self):
        text = (COMPACT_LOOP_MODES if self.compact else LOOP_MODES)[self.player.loop]
        self.loopButton.configure(text=text, style="TButton" if self.player.loop == "off" else "Accent.TButton")

    def showPlayButton(self):
        """Play / Playing / Pausing, or in the narrow two-player look the play or pause symbol"""
        if self.compact:
            text = "❚❚" if self.active and not self.player.paused else "⏵"
        else:
            text = ("Pausing" if self.player.paused else "Playing") if self.active else "Play"
        self.playButton.configure(text=text)

    def toggleMute(self):
        muted = not self.player.muted
        self.player.setMuted(muted)
        self.muteButton.configure(text="Unmute" if muted else "Mute", style="Accent.TButton" if muted else "TButton")

    @staticmethod
    def formatTime(seconds):
        return f"{int(seconds) // 60}:{int(seconds) % 60:02d}"

    def showProgress(self, pos, dur, reset=False):
        self.lyricClock[1] = (pos, time.time())
        if self.seeking and not reset:
            return # the user is dragging the bar, don't fight them
        self.seeking = False
        self.seekBar.configure(to=max(dur, 1))
        self.seekBar.set(pos)
        self.elapsed.configure(text=self.formatTime(pos))
        self.total.configure(text=self.formatTime(dur) if dur else ("" if reset else "LIVE"))
        self.chillSeek.configure(to=max(dur, 1)) # the Chill tab's copy of the bar
        self.chillSeek.set(pos)

    def onSeekRelease(self, slider=None):
        self.seeking = False
        self.player.seek((slider or self.seekBar).get())

    def playPlaylist(self):
        """The voice "playlist" command without a name: the original User_Music/coolPlaylist.xspf"""
        playlist = songFolderPath / "coolPlaylist.xspf"
        try:
            items = parsePlaylist(playlist)
        except (OSError, ET.ParseError) as e:
            self.logLine(f"Could not read playlist: {e}")
            return
        if items:
            self.player.play(items)
        else:
            self.logLine("No items found in playlist")

    # ---- settings ------------------------------------------------------------------------------------------------
    def markSwatch(self):
        for color, item in self.swatches:
            if color == ACCENT:
                x1, y1, x2, y2 = self.canvas.coords(item)
                self.canvas.coords(self.swatchRing, x1 - 4, y1 - 4, x2 + 4, y2 + 4)
                return
        self.canvas.coords(self.swatchRing, -99, -99, -99, -99) # a custom colour that isn't one of the circles

    def applyTheme(self, color, save=True):
        setAccent(color)
        self.tintTitleBars()
        for button in GlassButton.instances:
            button.repaint()
        for slider in GlassSlider.instances:
            self.canvas.itemconfigure(slider.fill, fill=ACCENT)
        self.canvas.itemconfigure(self.settingsThumb, fill=ACCENT)
        for bar in self.visBars + self.visBars2:
            self.canvas.itemconfigure(bar, fill=ACCENT)
        for lst in GlassList.instances:
            lst.queueDraw()
        for check in GlassCheck.instances:
            check.draw()
        self.markSwatch()
        if save:
            self.settings["accent"] = color
            self.persistSettings()

    def chooseCustomColor(self):
        picked = colorchooser.askcolor(color=ACCENT, parent=self.root, title=T("Choose a theme color"))[1]
        if picked:
            self.applyTheme(picked.lower())

    @staticmethod
    def eqText(db):
        return f"{db:+.1f} dB" if db else "0.0 dB"

    def setSettingsStatus(self, text, kind="info"):
        """Only problems are written on the page: what a setting did is already plain to see, so success clears the line"""
        self.settingsStatus.configure(text="" if kind == "ok" else text, foreground=STATUS_COLORS.get(kind, MUTED))

    def persistSettings(self):
        problem = saveSettings(self.settings)
        if problem:
            self.setSettingsStatus(problem, "error")

    def showBackgroundName(self):
        chosen = self.settings["background"]
        if chosen and Path(chosen).is_file():
            self.bgName.configure(text=Path(chosen).name)
        elif findBackground():
            self.bgName.configure(text=f"Default ({findBackground().name})")
        else:
            self.bgName.configure(text="None, put a .jpg or .png in the assets folder or choose one")
        night = self.settings["nightBackground"]
        self.nightName.configure(text=Path(night).name if night and Path(night).is_file() else "Default (the day picture, darkened)")

    # ---- an animated background (.gif) ----------------------------------------------------------------------------
    # It plays on the Chill tab and in mini mode, where the picture is what you look at. Elsewhere glass covers all of it
    # but a thin edge, and every new frame makes Tk redraw the whole page (glass, rows, text): a third of a processor
    # core for movement you'd hardly see, so those tabs show the first frame. The glass keeps the first frame's
    # frosting throughout, as blurring every panel again for every frame would cost far more
    BG_CACHE_BYTES = 200 * 1024 * 1024 # frames scaled to the window are kept while they fit in this, so later loops are cheap

    def playBackground(self, frames, size, box):
        """Starts the frames (or stops, with None) for a window of this size; box: the part of each frame that fills it"""
        if self.bgAnimationJob:
            self.root.after_cancel(self.bgAnimationJob)
            self.bgAnimationJob = None
        self.bgAnimation = None
        self.canvas.delete("bgframe")
        if not frames:
            return
        fits = len(frames) * size[0] * size[1] * 8 <= self.BG_CACHE_BYTES # a kept frame, and Tk's copy of it ready to draw
        self.bgAnimation = {"frames": frames, "size": size, "box": box, "at": 0, "scaled": {} if fits else None}
        if fits:
            self.keepFrame(0, self.bgPhoto)
        self.resumeBackground()

    def backgroundShows(self):
        return self.mini or self.currentTab == "chill"

    def resumeBackground(self):
        """Starts the frames going again on a tab that shows the picture (run on every tab change)"""
        if self.bgAnimation and not self.bgAnimationJob and self.backgroundShows():
            self.bgAnimationJob = self.root.after(self.bgAnimation["frames"][self.bgAnimation["at"]][1], self.nextBackgroundFrame)

    def keepFrame(self, at, photo):
        """Keeps a scaled frame, on a hidden item of its own: Tk throws away its ready-to-draw copy of a picture no item
        uses, and making that again every time the frame comes round costs more than drawing it"""
        self.bgAnimation["scaled"][at] = photo
        self.canvas.create_image(-9999, -9999, anchor="nw", image=photo, state="hidden", tags=("bgframe",))

    def showBackgroundFrame(self, at):
        animation = self.bgAnimation
        animation["at"] = at
        photo = animation["scaled"].get(at) if animation["scaled"] is not None else None
        if photo is None:
            photo = ImageTk.PhotoImage(animation["frames"][at][0].resize(animation["size"], Image.BILINEAR, box=animation["box"]))
            if animation["scaled"] is not None:
                self.keepFrame(at, photo)
        self.canvas.itemconfigure(self.bgItem, image=photo)
        self.bgPhoto = photo

    def nextBackgroundFrame(self):
        self.bgAnimationJob = None
        started = time.perf_counter()
        animation = self.bgAnimation
        if not self.backgroundShows(): # back to the first frame, until a tab that shows the picture
            if animation["at"]:
                self.showBackgroundFrame(0)
            return
        at = (animation["at"] + 1) % len(animation["frames"])
        if self.root.state() == "iconic":
            animation["at"] = at # nothing to see while minimized, so nothing drawn
        else:
            self.showBackgroundFrame(at)
        spent = int((time.perf_counter() - started) * 1000)
        self.bgAnimationJob = self.root.after(max(animation["frames"][at][1] - spent, 10), self.nextBackgroundFrame)

    def wantNight(self):
        return self.settings["nightMode"] and isNightHour(time.localtime().tm_hour)

    def currentBackground(self):
        """The playing song's cover (with Cover ticked), else the day or night picture. That one is kept, so going back
        to it after a song with a cover doesn't read it from disk again"""
        if self.settings["cover"] and self.artData:
            cover = loadCover(self.artData)
            if cover:
                return cover
        key = (self.nightActive, self.settings["background"], self.settings["nightBackground"] if self.nightActive else "")
        if self.plainBackground[0] != key:
            if self.nightActive:
                picture = loadNightBackground(self.settings["nightBackground"], self.settings["background"])
            else:
                picture = loadBackground(self.settings["background"])
            self.plainBackground = (key, picture)
        return self.plainBackground[1]

    def applyBackground(self, fade=False):
        """Shows the background that's wanted now. fade: blend into it (a new song, night coming or going)"""
        self.nightActive = self.wantNight()
        source = self.currentBackground()
        self.showBackgroundName()
        if source is self.bgSource and source is not None:
            return # the same picture: nothing to redo
        self.bgSource = source
        if not self.bgSource:
            self.canvas.itemconfigure(self.bgItem, image="")
        self.fadeNextBackground = fade
        self.relayout(self.canvas.winfo_width(), self.canvas.winfo_height())

    # ---- fades between backgrounds and between song names, kept cheap ------------------------------------------------
    # A background fade is a few blends of the old and new picture at the window's size (each one is one Pillow call
    # and one picture handed to Tk), done only on the Chill tab and in mini mode, where the picture is what you see.
    # A title fade only changes the text's colour, which costs Tk next to nothing
    BG_FADE_STEPS, BG_FADE_MS = 8, 40
    TITLE_FADE_STEPS, TITLE_FADE_MS = 6, 25 # each way
    TITLE_FADED = (22, 25, 32) # the colour a fading name heads for: about the glass behind it

    def fadeBackground(self, old, new, step):
        self.bgFadeJob = None
        if step >= self.BG_FADE_STEPS:
            self.canvas.itemconfigure(self.bgItem, image=self.bgPhoto)
            self.bgFadePhoto = None
            return
        self.bgFadePhoto = ImageTk.PhotoImage(Image.blend(old, new, step / self.BG_FADE_STEPS))
        self.canvas.itemconfigure(self.bgItem, image=self.bgFadePhoto)
        self.bgFadeJob = self.root.after(self.BG_FADE_MS, lambda: self.fadeBackground(old, new, step + 1))

    def cancelBackgroundFade(self):
        if self.bgFadeJob:
            self.root.after_cancel(self.bgFadeJob)
            self.bgFadeJob = self.bgFadePhoto = None

    def setTitle(self, text):
        """A new song name: the old one fades out, the new one fades in (straight away while minimized)"""
        if self.titleFadeJob:
            self.root.after_cancel(self.titleFadeJob)
            self.titleFadeJob = None
        if text == self.titleText or self.root.state() == "iconic":
            self.showTitle(text)
            self.tintTitles(0.0)
            return
        self.fadeTitle(text, 1)

    def fadeTitle(self, text, step):
        """Steps 1..N fade the old name out, then the new one is put in and steps N+1..2N fade it in"""
        self.titleFadeJob = None
        n = self.TITLE_FADE_STEPS
        if step == n:
            self.showTitle(text)
        self.tintTitles(step / n if step <= n else (2 * n - step) / n)
        if step < 2 * n:
            self.titleFadeJob = self.root.after(self.TITLE_FADE_MS, lambda: self.fadeTitle(text, step + 1))

    def tintTitles(self, amount):
        """Song names partly faded: 0 is their own colour, 1 all the way to the glass colour"""
        r, g, b = (round(c + (f - c) * amount) for c, f in zip(hexToRgb(TEXT), self.TITLE_FADED))
        for label in (self.nowPlaying, self.chillTitle, self.miniTitle):
            label.configure(foreground=f"#{r:02x}{g:02x}{b:02x}")

    def showTitle(self, text):
        self.titleText = text
        self.placeTitle()
        self.syncChill()
        self.syncMini()

    def setBackgroundAverage(self, color):
        """A new background picture (or window size): the title bar follows its colour when that changed"""
        if color != self.bgAverage:
            self.bgAverage = color
            if self.settings["pictureTitleBar"]:
                self.tintTitleBars()

    def togglePictureTitleBar(self):
        self.settings["pictureTitleBar"] = not self.settings["pictureTitleBar"]
        self.persistSettings()
        self.pictureTitleBarCheck.set(self.settings["pictureTitleBar"])
        self.tintTitleBars()
        self.setSettingsStatus("The title bar takes the background's average colour, and changes with it."
                               if self.settings["pictureTitleBar"] else "The title bar takes the theme colour.", "ok")

    def showLanguageMenu(self):
        """The language button: every language the app speaks, each in its own words"""
        bx, by = self.canvas.coords(self.languageButton.image)
        self.languageMenu.show(self.canvas.winfo_rootx() + int(bx), self.canvas.winfo_rooty() + int(by) + 38,
                               [{"label": name, "translate": False, "command": lambda code=code: self.chooseLanguage(code)}
                                for code, name in LANGUAGES.items()])

    def chooseLanguage(self, code):
        """Saves the language and restarts in it: every word on screen was drawn in the old one"""
        if code == LANGUAGE:
            return
        self.settings["language"] = code
        self.persistSettings()
        self.setSettingsStatus("Restarting...", "busy")
        self.root.after(300, self.restartApp)

    def restartApp(self):
        """Opens a new copy of the app (a moment later, once this one has let go of the media keys) and closes this one"""
        app = [sys.executable] if getattr(sys, "frozen", False) else [sys.executable, str(Path(__file__).resolve())]
        command = "ping -n 3 127.0.0.1 >nul & start \"\" " + " ".join(f'"{part}"' for part in app)
        # one string, not a list: a list would escape the quotes as \", which cmd doesn't understand (start then looks
        # for a program called \\). /s makes cmd take off just the outer quotes and run the rest as it is
        subprocess.Popen(f'cmd /s /c "{command}"', cwd=str(BASE_DIR), creationflags=subprocess.CREATE_NO_WINDOW)
        self.close()

    def toggleCover(self):
        self.settings["cover"] = not self.settings["cover"]
        self.persistSettings()
        self.coverCheck.set(self.settings["cover"])
        self.applyBackground()
        self.setSettingsStatus("The playing song's cover is the background (the picture above for songs without one)."
                               if self.settings["cover"] else "The picture above is the background.", "ok")

    def toggleNight(self):
        self.settings["nightMode"] = not self.settings["nightMode"]
        self.persistSettings()
        self.nightCheck.set(self.settings["nightMode"])
        self.applyBackground()
        self.setSettingsStatus("The night background is used from 9 PM until 7 AM." if self.settings["nightMode"]
                               else "The day background is always used.", "ok")

    # ---- fun: the "rick", "snow" and "rain" keywords, and weather that goes with the song ----------------------------
    SNOW_WORDS = re.compile(r"\b(?:christmas|snow|santa)(?:'s|s)?\b", re.IGNORECASE) # in the song's name or album
    RAIN_WORDS = re.compile(r"\b(?:rain|storm)(?:s|y|ing|drops?)?\b", re.IGNORECASE) # in the song's name only
    WEATHER_KEY = "#010203" # the colour the weather window is see-through in
    RAIN_SLANT = 0.2 # sideways distance for every step down

    def toggleFun(self):
        self.settings["fun"] = not self.settings["fun"]
        self.persistSettings()
        self.funCheck.set(self.settings["fun"])
        self.voiceRebuild = True # "rick", "snow" and "rain" join or leave the words the recogniser listens for
        if not self.settings["fun"]:
            self.forcedWeather.clear()
        self.updateWeather()
        self.setSettingsStatus('Fun is enabled. :)' if self.settings["fun"] else "This is sad. :(", "ok")

    def toggleYouTube(self):
        """YouTube songs in or out of the library and playlists. Switched off, they stay stored and come back when it's on"""
        self.settings["youtube"] = not self.settings["youtube"]
        self.persistSettings()
        self.youtubeCheck.set(self.settings["youtube"])
        if not self.settings["youtube"] and self.player.youtube.isOpen():
            self.stop() # a YouTube song is playing
        self.refreshSongs()
        self.refreshPlaylistTracks()
        if self.libGeometry:
            self.placeLibrary() # the +YT buttons come or go
            self.dirtyTabs.add("playlists") # placed again when it's next shown
        self.setSettingsStatus("", "ok")

    def updateWeather(self):
        """What falls: whatever was asked for by voice, snow for a Christmas, Snow or Santa song (name or album), and rain
        for a Rain or Storm song (the name only, not the album)"""
        wanted = set()
        if self.settings["fun"]:
            wanted |= self.forcedWeather
            if self.nowTrack:
                label, path = self.nowTrack
                if any(self.SNOW_WORDS.search(text) for text in (label, self.tagsOf(path)[1])):
                    wanted.add("snow")
                if self.RAIN_WORDS.search(label):
                    wanted.add("rain")
        self.setWeather(wanted)

    def setWeather(self, wanted):
        if wanted == self.weatherOn:
            return
        running = bool(self.weatherOn)
        self.weatherOn = set(wanted)
        if wanted and not running:
            # The flakes and drops live in their own see-through window laid over the player. Moving them on the player's own
            # canvas would repaint all of its frosted glass panels every frame, which used about half a processor core
            win = self.weatherWin = tk.Toplevel(self.root)
            win.overrideredirect(True)
            win.transient(self.root) # stays just above the player, and goes away when it is minimised
            win.configure(bg=self.WEATHER_KEY)
            win.attributes("-transparentcolor", self.WEATHER_KEY)
            self.weatherCanvas = tk.Canvas(win, bg=self.WEATHER_KEY, highlightthickness=0)
            self.weatherCanvas.pack(fill="both", expand=True)
            self.weatherGeometry, self.particles, self.weatherHidden = None, {}, False
            win.update_idletasks()
            self.letClicksThrough(win)
            self.weatherStep()
        elif not wanted:
            if self.weatherJob:
                self.root.after_cancel(self.weatherJob)
                self.weatherJob = None
            if self.weatherWin:
                self.weatherWin.destroy()
            self.weatherWin = self.weatherCanvas = None
            self.particles = {}
        else: # one kind stopped while another carries on
            for kind in [k for k in self.particles if k not in wanted]:
                for particle in self.particles.pop(kind):
                    self.weatherCanvas.delete(particle[0])

    def weatherHandles(self, win):
        import ctypes
        user32 = ctypes.windll.user32
        user32.GetWindow.restype = ctypes.c_void_p
        user32.SetWindowLongPtrW.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p]
        hwnd = user32.GetParent(win.winfo_id()) or win.winfo_id()
        owner = user32.GetParent(self.root.winfo_id()) or self.root.winfo_id()
        return user32, hwnd, owner

    def letClicksThrough(self, win):
        """Mouse clicks and the keyboard focus pass straight through the weather window to the player under it, and the
        player owns it, so it always stays directly above the player (and goes with it when it is minimised)"""
        user32, hwnd, owner = self.weatherHandles(win)
        user32.SetWindowLongPtrW(hwnd, -8, owner) # GWLP_HWNDPARENT: the owner
        style = user32.GetWindowLongW(hwnd, -20) # GWL_EXSTYLE
        # layered, click-through, no taskbar button, never activated
        user32.SetWindowLongW(hwnd, -20, style | 0x80000 | 0x20 | 0x80 | 0x08000000)
        win.lift(self.root) # straight above the player

    def keepClicksThrough(self, win):
        """Windows forgets the owner and the click-through style when the window is hidden and shown again (minimising
        and restoring the player does that), so they are put back whenever they are found missing"""
        user32, hwnd, owner = self.weatherHandles(win)
        if not user32.GetWindowLongW(hwnd, -20) & 0x20 or user32.GetWindow(hwnd, 4) != owner: # GW_OWNER
            self.letClicksThrough(win)

    def weatherStep(self):
        """Moves everything a little (15 times a second). It follows the player's window, whatever its size: the full
        window or the mini one"""
        root, main = self.root, self.canvas
        w, h = main.winfo_width(), main.winfo_height()
        if root.state() in ("iconic", "withdrawn") or w < 50 or h < 50: # minimised: nothing to see, so hardly any work
            if not self.weatherHidden:
                self.weatherWin.withdraw()
                self.weatherHidden = True
            self.weatherJob = root.after(500, self.weatherStep)
            return
        if self.weatherHidden:
            self.weatherWin.deiconify()
            self.weatherHidden = False
        self.keepClicksThrough(self.weatherWin)
        geometry = f"{w}x{h}+{main.winfo_rootx()}+{main.winfo_rooty()}"
        if geometry != self.weatherGeometry: # the player moved or changed size
            self.weatherWin.geometry(geometry)
            self.weatherGeometry = geometry
        self.weatherTick += 1
        if "snow" in self.weatherOn:
            self.stepSnow(w, h)
        if "rain" in self.weatherOn:
            self.stepRain(w, h)
        self.weatherJob = root.after(66, self.weatherStep) # 15 frames a second

    def stepSnow(self, w, h):
        canvas, flakes = self.weatherCanvas, self.particles.setdefault("snow", [])
        want = max(20, w * h // 10000)
        while len(flakes) < want:
            size = random.choice((1.5, 2, 2, 2.5, 3, 3.5, 4.5)) # bigger flakes are closer, so they fall faster
            item = canvas.create_oval(0, 0, 0, 0, fill=random.choice(("#ffffff", "#ffffff", "#e6ecfa")), outline="")
            flakes.append([item, random.uniform(0, w), random.uniform(0, h), size, 1.2 + size * 0.74, # px per frame
                           random.uniform(4, 14), random.uniform(0, 6.3)])
        while len(flakes) > want:
            canvas.delete(flakes.pop()[0])
        sway = self.weatherTick * 0.066
        for flake in flakes:
            item, x, y, size, speed, amplitude, phase = flake
            y += speed
            if y > h + size:
                y, x = -size, random.uniform(0, w)
                flake[1] = x
            flake[2] = y
            drift = x + math.sin(sway + phase) * amplitude
            canvas.coords(item, drift - size, y - size, drift + size, y + size)

    def stepRain(self, w, h):
        canvas, drops = self.weatherCanvas, self.particles.setdefault("rain", [])
        want = max(26, w * h // 7000)
        slant = self.RAIN_SLANT
        while len(drops) < want:
            length = random.uniform(9, 20) # longer drops are closer, so they fall faster
            item = canvas.create_line(0, 0, 0, 0, fill=random.choice(("#c3d4f5", "#a9bfe8", "#8fa9dc")), width=1 if length < 15 else 2)
            drops.append([item, random.uniform(-slant * h, w), random.uniform(0, h), length, 16 + length * 1.2]) # px per frame
        while len(drops) > want:
            canvas.delete(drops.pop()[0])
        for drop in drops:
            item, x, y, length, speed = drop
            x += speed * slant
            y += speed
            if y > h + length or x > w + length:
                y, x = -length, random.uniform(-slant * h, w)
            drop[1], drop[2] = x, y
            canvas.coords(item, x, y, x + length * slant, y + length)

    def chooseBackground(self, night=False):
        start = Path.home() / "Pictures"
        path = filedialog.askopenfilename(
            parent=self.root, title=T("Choose a night background picture" if night else "Choose a background picture"),
            filetypes=PICTURE_TYPES, initialdir=str(start if start.is_dir() else BASE_DIR))
        if not path:
            return
        try:
            with Image.open(path) as picture:
                picture.verify()
        except (OSError, ValueError, SyntaxError, Image.DecompressionBombError) as e:
            self.setSettingsStatus(f"Couldn't open that picture ({Path(path).name}): {e}", "error")
            return
        self.settings["nightBackground" if night else "background"] = str(Path(path))
        self.persistSettings()
        self.applyBackground()
        self.setSettingsStatus(f"{'Night background' if night else 'Background'} set to {Path(path).name}.", "ok")

    def resetBackground(self, night=False):
        self.settings["nightBackground" if night else "background"] = ""
        self.persistSettings()
        self.applyBackground()
        self.setSettingsStatus("Using the default night background." if night else "Using the default background.", "ok")

    def onEq(self, band, value):
        snapped = round(value * 2) / 2 # half-decibel steps
        _, slider, readout = self.eqRows[band]
        slider.set(snapped)
        readout.configure(text=self.eqText(snapped))
        self.settings["eq"][band] = snapped
        for player in self.players:
            player.setEq(*(self.settings["eq"][b] for b in ("bass", "mid", "treble")))

    @staticmethod
    def fadeText(seconds):
        return f"{seconds:.1f} s" if seconds else "Off"

    def onFade(self, key, value):
        snapped = round(value * 2) / 2 # half-second steps
        _, slider, readout = self.fadeRows[key]
        slider.set(snapped)
        readout.configure(text=self.fadeText(snapped))
        self.settings[key] = snapped
        for player in self.players:
            player.setFades(self.settings["fadeIn"], self.settings["fadeOut"])

    def resetFades(self):
        for key in self.fadeRows:
            self.onFade(key, 1.5)
        self.persistSettings()
        self.setSettingsStatus("Fades reset to 1.5 s.", "ok")

    def saveEq(self):
        """On slider release: saving on every drag step would write the file dozens of times"""
        self.persistSettings()

    def resetEq(self):
        for band in self.eqRows:
            self.onEq(band, 0)
        self.persistSettings()
        self.setSettingsStatus("Equalizer reset.", "ok")

    # ---- playlists -----------------------------------------------------------------------------------------------
    def setPlaylistStatus(self, text, kind="info"):
        self.playlistStatus.configure(text=text, foreground=STATUS_COLORS.get(kind, MUTED))

    def persistPlaylists(self):
        problem = savePlaylists(self.playlists)
        if problem:
            self.setPlaylistStatus(problem, "error")

    def selectedPlaylist(self):
        sel = self.playlistList.curselection()
        return self.playlists[self.playlistShown[sel[0]]] if sel and sel[0] < len(self.playlistShown) else None

    def refreshPlaylists(self, select=None, reveal=True):
        """Redraws the playlist list, narrowed by its search box. select: the index in self.playlists of the one to
        select. reveal: clear the search when it hides that one (a new playlist, one named by voice)"""
        if select is not None and not 0 <= select < len(self.playlists):
            select = None
        query = self.playlistSearch.text().lower()
        if reveal and select is not None and query not in self.playlists[select]["name"].lower():
            self.playlistSearch.setHint(self.playlistSearch.entry.focus_get() is not self.playlistSearch.entry)
            query = ""
        self.playlistShown = [i for i, playlist in enumerate(self.playlists) if query in playlist["name"].lower()]
        self.playlistList.delete(0, "end")
        for index in self.playlistShown:
            self.playlistList.insert("end", self.playlists[index]["name"])
        count = f"  ·  {len(self.playlistShown)} of {len(self.playlists)}" if query else ""
        self.playlistsLabel.configure(text=f"PLAYLISTS{count}")
        if select in self.playlistShown:
            self.playlistList.selection_set(self.playlistShown.index(select)) # also refreshes the songs on the right
        else:
            self.refreshPlaylistTracks()

    def onPlaylistSearch(self):
        """Typing in the playlist search: the selected playlist stays selected while it still matches"""
        current = self.selectedPlaylist()
        self.refreshPlaylists(self.playlists.index(current) if current else None, reveal=False)

    def onPlaylistMoved(self, old, new):
        """A playlist dragged from row old to row new. With the search narrowing the list, it takes the place of the
        playlist it was dropped on, so the rows still show the order they will have once the search is cleared"""
        self.playlists.insert(self.playlistShown[new], self.playlists.pop(self.playlistShown[old]))
        query = self.playlistSearch.text().lower()
        self.playlistShown = [i for i, playlist in enumerate(self.playlists) if query in playlist["name"].lower()]

    def showPlaylistMenu(self, event):
        playlist = self.selectedPlaylist()
        if not playlist:
            return
        others = [{"label": other["name"], "translate": False, "command": lambda other=other: self.addPlaylistToPlaylist(other, playlist)}
                  for other in self.playlists if other is not playlist]
        entries = [{"label": "Play", "command": self.playSelectedPlaylist},
                   {"label": "Add songs...", "command": self.addSongsToPlaylist}]
        if self.settings["youtube"]:
            entries.append({"label": "Add YouTube song...", "command": lambda: self.addYouTubeDialog(playlist)})
        entries += [{"label": "Add another playlist", "sub": others or [{"label": "No other playlists yet", "disabled": True}]},
                    None,
                    {"label": "Delete playlist", "command": self.askDeletePlaylist}]
        self.playlistMenu.show(event.x_root, event.y_root, entries)

    def addYouTubeToPlaylist(self):
        """The Playlists tab's +YT button: a YouTube song for the selected playlist (and the library)"""
        playlist = self.selectedPlaylist()
        if not playlist:
            self.setPlaylistStatus("Select or create a playlist first.", "error")
            return
        self.addYouTubeDialog(playlist)

    def addTracksToPlaylist(self, playlist, tracks):
        """Adds the songs the playlist doesn't have yet, saves it and redraws it. Returns how many were new"""
        have = {os.path.normcase(t) for t in playlist["tracks"]}
        new = [t for t in dict.fromkeys(str(t) for t in tracks) if os.path.normcase(t) not in have]
        playlist["tracks"] += new
        self.persistPlaylists()
        if self.selectedPlaylist() is playlist:
            self.refreshPlaylistTracks()
        return len(new)

    def addPlaylistToPlaylist(self, source, target):
        """Adds every song of one playlist to another (songs already in it are skipped; the first one stays as it is)"""
        added = self.addTracksToPlaylist(target, source["tracks"])
        skipped = len(set(os.path.normcase(t) for t in source["tracks"])) - added
        note = f" ({skipped} already in it)" if skipped else ""
        self.setPlaylistStatus(f"Added {added} song{'s' if added != 1 else ''} from {source['name']} to {target['name']}{note}.", "ok")

    def playlistView(self, playlist, search=True):
        """The playlist's songs as (name, path), in the order its sort buttons ask for, narrowed by the search box"""
        songs = [self.songOf(track) for track in playlist["tracks"] if self.settings["youtube"] or not isYouTube(track)]
        songs = self.sortedSongs(songs, playlist.get("sort", ""), playlist.get("reverse", False))
        query = self.trackSearch.text().lower() if search else ""
        return [song for song in songs if not query or self.matches(song, query)]

    def refreshPlaylistTracks(self):
        playlist = self.selectedPlaylist()
        self.trackList.delete(0, "end")
        self.showPlaylistSortButtons()
        if not playlist:
            self.tracksLabel.configure(text="SONGS")
            return
        shown = self.playlistView(playlist)
        count = f"  ·  {len(shown)} of {len(playlist['tracks'])}" if self.trackSearch.text() else ""
        self.tracksLabel.configure(text=f"SONGS  ·  {playlist['name']}{count}")
        for name, path in shown:
            self.trackList.insert("end", self.songRow(name, path))
        if playlist.get("sort") == "album":
            self.trackList.breaks = self.albumBreaks(shown)

    def setPlaylistSort(self, mode):
        playlist = self.selectedPlaylist()
        if not playlist:
            self.setPlaylistStatus("Select a playlist to sort first.", "error")
            return
        if playlist.get("sort") == mode:
            playlist["reverse"] = not playlist.get("reverse", False) # pressing the active one flips the order
        else:
            playlist["sort"], playlist["reverse"] = mode, False
        self.persistPlaylists()
        self.refreshPlaylistTracks()

    def showPlaylistSortButtons(self):
        playlist = self.selectedPlaylist()
        for mode, button in self.playlistSortButtons.items():
            on = bool(playlist) and playlist.get("sort", "") == mode
            arrow = " ▼" if on and playlist.get("reverse") else " ▲" if on else ""
            button.configure(text=T(dict(LIST_SORT_MODES)[mode]) + arrow, style="Accent.TButton" if on else "TButton")

    def playSelectedPlaylist(self):
        playlist = self.selectedPlaylist()
        if not playlist:
            return
        if not playlist["tracks"]:
            self.setPlaylistStatus(f"{playlist['name']} is empty. Use Add songs... first.")
            return
        self.player.play(self.playlistView(playlist, search=False)) # the whole playlist, whatever is typed in the search
        self.setPlaylistStatus(f"Playing {playlist['name']}", "ok")

    def playSelectedTrack(self):
        playlist, sel = self.selectedPlaylist(), self.trackList.curselection()
        if playlist and sel:
            self.player.play(self.playlistView(playlist), sel[0]) # the rest of the playlist follows

    def addSongsToPlaylist(self):
        playlist = self.selectedPlaylist()
        if not playlist:
            self.setPlaylistStatus("Select or create a playlist first.", "error")
            return
        paths = filedialog.askopenfilenames(
            parent=self.root, title=f"Add songs to {playlist['name']}", filetypes=SONG_TYPES,
            initialdir=str(songFolderPath if songFolderPath.is_dir() else Path.home()))
        new = [str(Path(p)) for p in paths if str(Path(p)) not in playlist["tracks"]]
        if not new:
            return
        playlist["tracks"] += new
        fresh = self.addToLibrary(new) # anything in a playlist belongs in the library too
        if fresh:
            self.persistLibrary()
            self.refreshSongs()
        self.persistPlaylists()
        self.refreshPlaylistTracks()
        extra = f" ({len(fresh)} new to the library too)" if fresh else ""
        self.setPlaylistStatus(f"Added {len(new)} song(s) to {playlist['name']}{extra}.", "ok")

    def onPlaylistSelect(self):
        self.playlistsListUsed = self.playlistList
        self.refreshPlaylistTracks()

    def onTrackSelect(self):
        """Picking songs in the playlist: with several picked, the status line says how many and where the options are"""
        self.playlistsListUsed = self.trackList
        count = len(self.trackList.indices())
        if count > 1:
            self.setPlaylistStatus(f"{count} songs selected  ·  right-click for options", "busy")
            self.trackCountShown = True
        elif self.trackCountShown: # back to one song: the count goes, other messages stay
            self.setPlaylistStatus("")
            self.trackCountShown = False

    def selectedTracks(self):
        """The (name, path) of every selected song in the open playlist"""
        playlist = self.selectedPlaylist()
        view = self.playlistView(playlist) if playlist else []
        return [view[i] for i in self.trackList.indices() if i < len(view)]

    def showTrackMenu(self, event):
        """Right-click menu for the playlist's songs. It acts on every selected song, like the library's"""
        playlist, songs = self.selectedPlaylist(), self.selectedTracks()
        if not playlist or not songs:
            return
        count = len(songs)
        self.trackMenu.show(event.x_root, event.y_root, [
            {"label": f"Play (the first of {count})" if count > 1 else "Play", "command": self.playSelectedTrack},
            self.editEntry(songs),
            None,
            {"label": f"Remove {count} songs from {playlist['name']}" if count > 1 else f"Remove from {playlist['name']}",
             "command": self.removeSelectedTrack},
        ])

    def removeSelectedTrack(self):
        """Takes the selected songs out of the open playlist, straight away (the library and the files are untouched)"""
        playlist, songs = self.selectedPlaylist(), self.selectedTracks()
        if not playlist or not songs:
            return
        gone = {os.path.normcase(str(path)) for _, path in songs}
        playlist["tracks"] = [t for t in playlist["tracks"] if os.path.normcase(str(self.songOf(t)[1])) not in gone]
        self.persistPlaylists()
        self.refreshPlaylistTracks()
        what = songs[0][0] if len(songs) == 1 else f"{len(songs)} songs"
        self.setPlaylistStatus(f"Removed {what} from {playlist['name']}.")

    def addPlaylistDialog(self, songs=()):
        """Makes a playlist: empty from the Playlists tab, or starting with the songs picked in the library's menu"""
        dialog = GlassDialog(self, "New playlist", 420, 230)
        dialog.label("NEW PLAYLIST", 28, 24, 12, True, TEXT)
        if songs:
            dialog.label(f"with {songs[0][0] if len(songs) == 1 else f'the {len(songs)} selected songs'}", 160, 27, 9, False, MUTED, 232)
        dialog.label("NAME", 28, 62)
        nameEntry = dialog.field(28, 80, 364)
        problem = dialog.label("", 28, 128, 9, False, "#ff7b7b", 364)

        def submit(event=None):
            name = nameEntry.get().strip()
            if not name:
                problem.configure(text="Give the playlist a name.")
            elif any(pl["name"].lower() == name.lower() for pl in self.playlists):
                problem.configure(text="You already have a playlist with that name.")
            else:
                tracks = list(dict.fromkeys(str(path) for _, path in songs))
                self.playlists.append({"name": name, "tracks": tracks, "sort": "", "reverse": False})
                self.persistPlaylists()
                self.refreshPlaylists(len(self.playlists) - 1)
                self.voiceRebuild = True # "playlist <name>" is new to the recogniser
                if tracks:
                    message = f"Made {name} with {len(tracks)} song{'s' if len(tracks) != 1 else ''}."
                    self.setPlaylistStatus(message, "ok")
                    self.logFlash(message)
                else:
                    self.setPlaylistStatus(f"Created {name}. Use Add songs... to fill it.", "ok")
                dialog.close()
            return "break"

        dialog.button("Create", 420 - 28 - 110, 230 - 62, 110, submit, "accent")
        dialog.button("Cancel", 420 - 28 - 110 - 8 - 90, 230 - 62, 90, dialog.close)
        dialog.onReturn(submit)
        dialog.show(nameEntry)

    def confirmDialog(self, message, confirmText="Delete"):
        """Modal ARE YOU SURE? window. Returns True only if the person presses the confirm button."""
        answer = {"yes": False}
        dialog = GlassDialog(self, "Are you sure?", 460, 230)
        dialog.label("ARE YOU SURE?", 28, 24, 18, True, TEXT)
        dialog.label(message, 28, 66, 10, False, TEXT, 404)

        def accept():
            answer["yes"] = True
            dialog.close()

        dialog.button(confirmText, 460 - 28 - 110, 230 - 62, 110, accept, "danger")
        dialog.button("Cancel", 460 - 28 - 110 - 8 - 100, 230 - 62, 100, dialog.close, "accent")
        dialog.onReturn(lambda e: dialog.close()) # Cancel is the default, so a stray Enter can't delete anything
        dialog.show()
        dialog.win.wait_window()
        return answer["yes"]

    def askDeletePlaylist(self):
        playlist = self.selectedPlaylist()
        if not playlist:
            self.setPlaylistStatus("Select a playlist to delete first.", "error")
            return
        count = len(playlist["tracks"])
        detail = f" It has {count} song{'s' if count != 1 else ''} in it." if count else ""
        if not self.confirmDialog(f"Delete the playlist \"{playlist['name']}\"?{detail} This can't be undone. Your music files are not touched."):
            return
        row = self.playlistList.curselection()[0]
        self.playlists.remove(playlist)
        self.persistPlaylists()
        self.voiceRebuild = True # "playlist <name>" leaves the words the recogniser listens for
        self.refreshPlaylists(reveal=False)
        if self.playlistShown: # the one that took its row, or the last one
            self.playlistList.selection_set(min(row, len(self.playlistShown) - 1))
        self.setPlaylistStatus(f"Deleted {playlist['name']}.")

    # ---- radio ---------------------------------------------------------------------------------------------------
    def stationInText(self, text):
        """The station whose name is spoken in the text (whole words, longest name wins), or None"""
        text = text.lower()
        for station in sorted(self.stations, key=lambda st: -len(st["name"])):
            if re.search(r"\b" + re.escape(station["name"].lower()) + r"\b", text):
                return station
        return None

    def mentionsRadio(self, text):
        return "radio" in text.lower() or self.stationInText(text) is not None

    def refreshStations(self, select=None):
        self.stationList.delete(0, "end")
        for station in self.stations:
            self.stationList.insert("end", station["name"])
        if select is not None and 0 <= select < len(self.stations):
            self.stationList.selection_set(select)
            self.stationList.see(select)

    def setRadioStatus(self, text, kind="info"):
        self.radioStatus.configure(text=text, foreground=ACCENT if kind == "busy" else STATUS_COLORS.get(kind, MUTED))

    def playSelectedStation(self):
        sel = self.stationList.curselection()
        if sel:
            self.playStation(self.stations[sel[0]])

    def playStation(self, station, channel=1):
        name = station["name"]
        if channel == 2:
            self.setDual(True)
        self.stationRequest += 1
        self.logLine(f"Playing {name} radio")
        self.setRadioStatus(f"Connecting to {name}...", "busy")
        threading.Thread(target=self.checkAndPlayStation, args=(station, self.stationRequest, channel), daemon=True).start()

    def checkAndPlayStation(self, station, request, channel=1):
        """Background thread: checks the stream first, so a dead station gets a plain-language reason"""
        name = station["name"]
        problem = checkStream(station["url"])
        if request != self.stationRequest:
            return # a newer click wins
        if problem:
            self.events.put(("radioStatus", f"Can't play {name}: {problem}", "error"))
            self.events.put(("log", f"Can't play {name}: {problem}"))
            return
        self.players[channel - 1].play([(f"{name} radio", station["url"])])
        self.events.put(("radioStatus", f"Playing {name}" + (" on player 2" if channel == 2 else ""), "ok"))

    def removeStation(self):
        sel = self.stationList.curselection()
        if not sel:
            self.setRadioStatus("Select a station to remove first.")
            return
        removed = self.stations.pop(sel[0])
        self.persistStations()
        self.refreshStations(min(sel[0], len(self.stations) - 1))
        self.setRadioStatus(f"Removed {removed['name']}.")

    def persistStations(self):
        problem = saveStations(self.stations)
        if problem:
            self.setRadioStatus(problem, "error")

    def onStationMoved(self, old, new):
        self.stations.insert(new, self.stations.pop(old))

    def addStationDialog(self):
        dialog = GlassDialog(self, "Add radio station", 460, 300)
        dialog.label("ADD RADIO STATION", 28, 24, 12, True, TEXT)
        dialog.label("NAME", 28, 62)
        nameEntry = dialog.field(28, 80, 404)
        dialog.label("STREAM URL  (the http:// or https:// address of the audio stream)", 28, 132)
        urlEntry = dialog.field(28, 150, 404)
        problem = dialog.label("", 28, 198, 9, False, "#ff7b7b", 404)

        def submit(event=None):
            name, url = nameEntry.get().strip(), urlEntry.get().strip()
            parsed = urlparse(url)
            if not name:
                problem.configure(text="Give the station a name.")
            elif parsed.scheme not in ("http", "https") or not parsed.netloc:
                problem.configure(text="The URL must start with http:// or https:// and include a server name.")
            elif any(st["url"] == url for st in self.stations):
                problem.configure(text="That stream is already in your list.")
            else:
                self.stations.append({"name": name, "url": url})
                self.persistStations()
                self.refreshStations(len(self.stations) - 1)
                dialog.close()
                self.playStation(self.stations[-1]) # connecting right away shows whether the address works
            return "break"

        dialog.button("Add and play", 460 - 28 - 140, 300 - 62, 140, submit, "accent")
        dialog.button("Cancel", 460 - 28 - 140 - 8 - 90, 300 - 62, 90, dialog.close)
        dialog.onReturn(submit)
        dialog.show(nameEntry)

    # ---- YouTube songs -------------------------------------------------------------------------------------------
    def addYouTubeDialog(self, playlist=None):
        """Adds a YouTube song to the library, and also to the playlist when one is given (from its right-click menu)"""
        dialog = GlassDialog(self, "Add YouTube song", 460, 240)
        dialog.label("ADD A YOUTUBE SONG", 28, 24, 12, True, TEXT)
        if playlist:
            dialog.label(f"to {playlist['name']}", 222, 27, 9, False, MUTED, 210)
        dialog.label("YOUTUBE LINK  (from the address bar, or Share > Copy)", 28, 62)
        urlEntry = dialog.field(28, 80, 404)
        problem = dialog.label("", 28, 128, 9, False, "#ff7b7b", 404)
        try:
            copied = self.root.clipboard_get().strip()
        except tk.TclError:
            copied = "" # nothing (or not text) on the clipboard
        if youTubeId(copied) and len(copied) < 300: # a link that was just copied is filled in already
            urlEntry.insert(0, copied)

        def submit(event=None):
            videoId = youTubeId(urlEntry.get())
            url = YT_WATCH + videoId if videoId else None
            if not videoId:
                problem.configure(text="That isn't a YouTube link. It looks like youtube.com/watch?v=... or youtu.be/...")
            elif playlist and url in playlist["tracks"]:
                problem.configure(text=f"That video is already in {playlist['name']}.")
            elif url in self.libraryPaths and not playlist:
                problem.configure(text="That video is already in your library.")
            elif url in self.libraryPaths: # in the library already: nothing to look up, it just joins the playlist
                dialog.close()
                self.addTracksToPlaylist(playlist, [url])
                self.setPlaylistStatus(f"Added {self.songOf(url)[0]} to {playlist['name']}.", "ok")
            else:
                dialog.close()
                self.logFlash("Looking it up on YouTube...")
                if playlist:
                    self.setPlaylistStatus("Looking it up on YouTube...", "busy")
                threading.Thread(target=self.lookUpYouTube, args=(videoId, playlist), daemon=True).start()
            return "break"

        dialog.button("Add", 460 - 28 - 110, 240 - 62, 110, submit, "accent")
        dialog.button("Cancel", 460 - 28 - 110 - 8 - 90, 240 - 62, 90, dialog.close)
        dialog.onReturn(submit)
        dialog.show(urlEntry)

    def lookUpYouTube(self, videoId, playlist=None):
        """Background thread: the video's title, channel and thumbnail"""
        try:
            title, channel = fetchYouTubeInfo(videoId)
        except ValueError as e:
            self.events.put(("logFlash", f"Couldn't add that YouTube song: {e}"))
            if playlist:
                self.events.put(("playlistStatus", f"Couldn't add that YouTube song: {e}", "error"))
            return
        self.events.put(("youtubeAdded", videoId, title, channel, playlist))

    def finishYouTube(self, videoId, title, channel, playlist=None):
        """Adds a looked-up YouTube song to the library, and to the playlist it was added from (if that still exists).
        Its title and channel are kept with the song files' tags"""
        url = YT_WATCH + videoId
        self.tagCache[os.path.normcase(url)] = {"m": "youtube", "title": title, "artist": channel, "album": "", "track": 0}
        saveTagCache(self.tagCache)
        if url not in self.libraryPaths:
            self.libraryPaths.append(url)
            self.persistLibrary()
        self.refreshSongs()
        if playlist and any(p is playlist for p in self.playlists): # it may have been deleted during the look-up
            self.addTracksToPlaylist(playlist, [url])
            message = f"Added {YT_TAG}{title} to {playlist['name']} and the library."
            self.setPlaylistStatus(message, "ok")
        else:
            message = f"Added {YT_TAG}{title} to the library."
        self.logFlash(message)

    # ---- voice commands ------------------------------------------------------------------------------------------
    @staticmethod
    def normalize(text):
        """Lower case, letters and digits only, so "Guile's Thorn" and "guiles thorn" compare equal"""
        return " ".join(re.sub(r"[^a-z0-9]+", " ", text.lower()).split())

    def songIndexInText(self, text):
        """Index in allSongs of the song named in the text: the longest exact name, else a close spelling, else None"""
        spoken = self.normalize(text)
        names = [self.normalize(plainName(name)) for name, _ in self.allSongs]
        found = [(len(n), i) for i, n in enumerate(names) if n and re.search(r"\b" + re.escape(n) + r"\b", spoken)]
        if found:
            return max(found)[1] # the longest name that was spoken
        wanted = re.split(r"\b(?:play|song)\b", spoken, maxsplit=1)[-1].strip()
        for prefix in ("the song ", "song ", "the "):
            if wanted.startswith(prefix):
                wanted = wanted[len(prefix):]
        close = difflib.get_close_matches(wanted, names, n=1, cutoff=0.78) if wanted else []
        return names.index(close[0]) if close else None

    def playSongNumber(self, index):
        if self.search.text(): # the spoken song may not match the search, so show everything again
            self.search.clear()
        self.listbox.select(index)
        self.player.play(self.songs, index) # the rest of the library follows, so Next/Prev work

    def handleCommand(self, text):
        """Acts on one recognised phrase (see the keyword list at the top of the file)"""
        text = text.lower()
        station = self.stationInText(text)
        asksToPlay = bool(re.search(r"\bplay\b", text)) and "playlist" not in text # "playing" doesn't count
        song = self.songIndexInText(text) if (asksToPlay or "song" in text) else None
        if station and asksToPlay and "song" not in text:
            self.playStation(station) # "play jazz"
        elif song is not None:
            self.playSongNumber(song) # "play ontario", "song party van"
        elif "you suck" in text or "exit" in text or re.search(r"\bend\b", text): # (whole word: not "weekend")
            self.close()
        elif "stop" in text:
            self.stop()
            if self.active2: # the second player stops too (its panel stays open, ready for another song)
                self.player2.stop()
                self.reset2()
        elif "pause" in text:
            if self.active and not self.player.paused:
                self.player.togglePause()
        elif "resume" in text or "continue" in text:
            if self.player.paused:
                self.player.togglePause()
        elif "next" in text or "skip" in text:
            self.player.next()
        elif "previous" in text or "back" in text:
            self.player.previous()
        elif "mute" in text:
            wantMuted = "unmute" not in text and "i'm mute" not in text # ("i'm mute" is how "unmute" was sometimes heard)
            if self.player.muted != wantMuted: # otherwise it's already in the requested state
                self.toggleMute()
        elif "time" in text:
            self.logLine(formatTime(LANGUAGE, time.localtime()))
        elif "date" in text:
            self.logLine(formatDate(LANGUAGE, time.localtime()))
        elif "rick" in text and self.settings["fun"]:
            self.player.play([("Never Gonna Give You Up", songFolderPath / "Never Gonna Give You Up.m4a")])
        elif "snow" in text and self.settings["fun"]:
            self.forcedWeather.add("snow")
            self.updateWeather()
        elif "rain" in text and self.settings["fun"]:
            self.forcedWeather.add("rain")
            self.updateWeather()
        elif "playlist" in text:
            for index, playlist in enumerate(self.playlists):
                if playlist["name"].lower() in text:
                    self.refreshPlaylists(index) # selects it, clearing the search if it hides it
                    self.playSelectedPlaylist()
                    break
            else:
                self.playPlaylist() # no saved playlist named: the original coolPlaylist.xspf
        elif "radio" in text:
            if station:
                self.playStation(station)

    # ---- voice on / off -------------------------------------------------------------------------------------------
    def setVoiceState(self, on):
        self.voiceOn = on
        self.refreshLogVisibility()
        self.placeVoiceInfo()
        self.voiceButton.configure(text="Voice: On" if on else "Voice: Off", style="Accent.TButton" if on else "TButton")

    # what voice control understands, for the i button's window ("rick" stays a surprise)
    VOICE_HELP = [
        ("play <song>  ·  song <song>", "plays a song from your library"),
        ("playlist <name>", "plays one of your playlists"),
        ("play <station>  ·  radio <station>", "plays a radio station"),
        ("pause  ·  resume  ·  continue", "pauses and carries on"),
        ("stop", "stops the music (both players)"),
        ("next  ·  skip", "goes to the next song"),
        ("previous  ·  back", "goes back a song"),
        ("mute  ·  unmute", "turns the sound off and on again"),
        ("time  ·  date", "shows it in the message box"),
        ("snow  ·  rain", "falls over the window until you say stop"),
        ("exit  ·  end", "closes Lettuce Player"),
    ]

    def showVoiceHelp(self):
        """The i button: every phrase voice control acts on, and the names it knows (songs, playlists, stations)"""
        width, height = 560, 600
        dialog = GlassDialog(self, "Voice commands", width, height)
        x, wide = 28, width - 56
        dialog.label("VOICE COMMANDS", x, 24, 12, True, TEXT)
        if LANGUAGE != "en":
            dialog.label("Voice control listens for English words", x + 210, 30, 9, False, MUTED, wide - 210)
        y = 60
        for phrase, meaning in self.VOICE_HELP:
            if phrase.startswith("snow") and not self.settings["fun"]:
                meaning += " (tick Fun in Settings)"
            GlassLabel(dialog.canvas, phrase, 10, True, TEXT, translate=False).place(x, y) # (said in English)
            dialog.label(meaning, x + 252, y + 1, 9, False, MUTED, wide - 252)
            y += 26
        y += 14
        dialog.label("WHAT IT KNOWS BY NAME", x, y, 9, True, MUTED)
        y += 24
        try:
            _, spoken, total = self.voiceGrammar() # the same list the recogniser listens for
        except Exception:
            spoken, total = None, len(self.allSongs)
        kinds = "music files (mp3, m4a, mp4, wav and wma) in User_Music and the ones you dropped in"
        if self.settings["youtube"]:
            kinds += ", and YouTube songs by their title"
        count = f"{spoken} of your {total} songs" if spoken is not None else f"Your {total} songs"
        lines = [
            f"{count}: {kinds}. Say a song's name as it shows in the list.",
            "A name with a word the speech model doesn't know (like a made-up word or a number written as one) can't be "
            "said, so those songs are left out.",
            "Playlists: " + (", ".join(pl["name"] for pl in self.playlists) or "none yet"),
            "Radio stations: " + (", ".join(st["name"] for st in self.stations) or "none yet"),
        ]
        font = tkfont.Font(family=FONT, size=9)
        for line in lines:
            label = dialog.label(line, x, y, 9, False, TEXT, wide)
            y += 6 + 16 * wrappedLines(font, line, wide) # (its lines, then a little space)
        dialog.button("Close", width - 28 - 110, height - 28 - 36, 110, dialog.close, "accent")
        dialog.show()

    def toggleVoice(self):
        if self.stopListening:
            self.stopListening(wait_for_stop=False)
            self.stopListening = None
            self.setVoiceState(False)
            return
        self.voiceButton.configure(text="Voice: ...")
        threading.Thread(target=self.startVoice, daemon=True).start()

    # ---- voice: offline, with Vosk -----------------------------------------------------------------------
    def voiceGrammar(self):
        """Everything the recogniser may hear: the commands, station and playlist names, and "play <song>" for each song.
        Limiting it to these makes it far more accurate than open dictation. Phrases with a word the model doesn't know
        (like "24apart") are left out, since it could never match them."""
        def clean(text):
            return " ".join(re.sub(r"[^a-z0-9' ]+", " ", text.lower()).split())

        phrases = set(VOICE_COMMANDS)
        if not self.settings["fun"]:
            phrases -= {"rick", "snow", "rain"}
        for station in self.stations:
            name = clean(station["name"])
            phrases |= {name, f"play {name}", f"radio {name}"}
        for playlist in self.playlists:
            name = clean(playlist["name"])
            phrases |= {f"playlist {name}", f"play playlist {name}"}
        songs = 0
        for name, _ in self.allSongs:
            name = clean(plainName(name)) # "play <title>" for a YouTube song, without the tag
            if name:
                phrases |= {f"play {name}", f"song {name}"}
                songs += 1
        known = [p for p in phrases if p and all(self.voskModel.vosk_model_find_word(w) != -1 for w in p.split())]
        spoken = sum(1 for name, _ in self.allSongs if clean(plainName(name)) and f"play {clean(plainName(name))}" in known)
        return json.dumps(known + ["[unk]"]), spoken, len(self.allSongs)

    def startVoice(self):
        """Background thread: loads the model, opens the microphone, then turns what it hears into "voice" events"""
        try:
            import pyaudio
            import vosk
            vosk.SetLogLevel(-1)
            if not self.voskModel:
                modelPath = resourcePath(VOSK_DIR)
                if not (modelPath / "am").is_dir():
                    raise FileNotFoundError(f"the speech model is missing, expected it in {modelPath}")
                self.voskModel = vosk.Model(str(modelPath))
            grammar, spoken, total = self.voiceGrammar()
            recognizer = vosk.KaldiRecognizer(self.voskModel, 16000, grammar)
            audio = pyaudio.PyAudio()
            stream = audio.open(format=pyaudio.paInt16, channels=1, rate=16000, input=True, frames_per_buffer=4000)
        except Exception as e:
            self.events.put(("logFlash", f"Voice unavailable: {e}"))
            self.events.put(("voiceState", False))
            return
        stop = threading.Event()
        self.stopListening = lambda wait_for_stop=False: stop.set()
        self.voiceRebuild = False
        self.events.put(("voiceState", True))
        self.events.put(("log", f"Listening offline. {spoken} of {total} songs can be asked for by name."))
        try:
            while not stop.is_set():
                if self.voiceRebuild: # songs, stations or playlists changed
                    self.voiceRebuild = False
                    recognizer = vosk.KaldiRecognizer(self.voskModel, 16000, self.voiceGrammar()[0])
                data = stream.read(4000, exception_on_overflow=False)
                if recognizer.AcceptWaveform(data):
                    text = " ".join(w for w in json.loads(recognizer.Result()).get("text", "").split() if w != "[unk]")
                    if text:
                        self.events.put(("voice", text))
        except Exception as e:
            self.events.put(("logFlash", f"Voice stopped: {e}"))
            self.events.put(("voiceState", False))
            self.stopListening = None
        finally:
            stream.stop_stream()
            stream.close()
            audio.terminate()

    # ---- voice: the Google version, switched off (needs internet) ----------------------------------------
    # To switch back: uncomment these, delete the Vosk startVoice above, and in __init__ add self.sr = None and
    # self.recognizer = None.
    # def startVoice(self):
    #     try:
    #         import speech_recognition as sr
    #         self.sr = sr
    #         self.recognizer = sr.Recognizer()
    #         mic = sr.Microphone()
    #         with mic as source:
    #             self.recognizer.adjust_for_ambient_noise(source, duration=0.5)
    #     except Exception as e:
    #         self.events.put(("logFlash", f"Microphone unavailable (is PyAudio installed?): {e}"))
    #         self.events.put(("voiceState", False))
    #         return
    #     self.stopListening = self.recognizer.listen_in_background(mic, self.onAudio, phrase_time_limit=8)
    #     self.events.put(("voiceState", True))
    #
    # def onAudio(self, recognizer, audio):
    #     try:
    #         self.events.put(("voice", recognizer.recognize_google(audio).lower()))
    #     except self.sr.UnknownValueError:
    #         pass
    #     except self.sr.RequestError as e:
    #         self.events.put(("logFlash", f"Speech service request failed: {e}"))

    def close(self):
        if self.stopListening:
            self.stopListening(wait_for_stop=False)
        self.player.close()
        self.player2.close()
        self.root.destroy()

def main():
    moveOldFiles()
    root = TkinterDnD.Tk()
    App(root)
    root.mainloop()
    os._exit(0) # the window is gone: end the process even if a background thread (microphone, media keys) is still blocked

if __name__ == '__main__':
    main()
