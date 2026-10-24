@echo off
rem Builds LettucePlayer.exe next to User_Music. Run from anywhere: build.bat
cd /d "%~dp0"

taskkill /IM LettucePlayer.exe /F >nul 2>&1

rem the speech model goes in without its general language model, graph\Gr.fst (24 MB): the app always listens for its
rem own list of phrases, which needs only the model's word list (written out as words.txt). vosk_model stays whole
if exist model_build rmdir /s /q model_build
xcopy /e /i /q /y vosk_model model_build\vosk_model >nul
Scripts\python.exe tools\vosk_words.py model_build\vosk_model\graph\Gr.fst model_build\vosk_model\graph\words.txt
if errorlevel 1 (
    echo Couldn't make the speech model's word list.
    exit /b 1
)
del model_build\vosk_model\graph\Gr.fst

rem --onedir: the app's files sit in _internal beside the exe, so it opens in under a second. A --onefile exe has to
rem unpack all of them to a temp folder on every launch, which took 4 to 5 seconds.
rem Left out: Pillow's AVIF pictures (7.6 MB; the picture choosers don't offer them), its text drawing (2.2 MB; the
rem app draws shapes with it, never text) and its colour profiles (0.3 MB). Pillow carries on without them. Also left
rem out: websockets, and the asyncio, multiprocessing and concurrent it brings (1 MB). They come with Vosk for its file
rem transcriber and model downloader, which the app doesn't use; nothing else imports them
Scripts\python.exe -m PyInstaller --noconfirm --onedir --windowed --name LettucePlayer --icon "%~dp0assets\LettucePlayer.ico" --add-data "%~dp0assets\LettucePlayer.ico;assets" --add-data "%~dp0audio_engine;audio_engine" --add-data "%~dp0model_build\vosk_model;vosk_model" --collect-all vosk --exclude-module PIL._avif --exclude-module PIL.AvifImagePlugin --exclude-module PIL._imagingft --exclude-module PIL._imagingcms --exclude-module websockets --exclude-module asyncio --exclude-module multiprocessing --exclude-module concurrent --distpath dist --workpath build --specpath build speechVLC2.py
if errorlevel 1 (
    echo Build failed.
    exit /b 1
)

rem the exe needs its _internal folder next to it, so both are copied (the old _internal goes first)
copy /y dist\LettucePlayer\LettucePlayer.exe LettucePlayer.exe >nul
if exist _internal rmdir /s /q _internal
xcopy /e /i /q /y dist\LettucePlayer\_internal _internal >nul
rem Tcl's time zone tables (2.3 MB) are only for its "clock" command, which nothing in the app uses
if exist _internal\_tcl_data\tzdata rmdir /s /q _internal\_tcl_data\tzdata 2>nul
rem (freshly copied files can be held open for a moment, by an antivirus scan for one: then a second go)
if exist _internal\_tcl_data\tzdata (
    timeout /t 1 /nobreak >nul
    rmdir /s /q _internal\_tcl_data\tzdata
)
rem More of Tcl and Tk that nothing uses: the clock's translations, Tk's translations (it falls back to its built-in
rem English), Tk's demo pictures, and Tcl's test kit and web libraries
for %%d in (_tcl_data\msgs _tk_data\msgs _tk_data\images _tcl_data\http1.0) do if exist "_internal\%%d" rmdir /s /q "_internal\%%d"
del /q _internal\tcl8\8.5\tcltest-*.tm _internal\tcl8\8.6\http-*.tm 2>nul
rem Of Tcl's text encodings, only those a Windows PC can be set to (its code pages, Japanese, Chinese and Korean
rem included) and a few basics are kept; the rest are for other systems
set "KEEPENC= ascii iso8859-1 symbol dingbats cp437 cp850 cp874 cp932 cp936 cp949 cp950 cp1250 cp1251 cp1252 cp1253 cp1254 cp1255 cp1256 cp1257 cp1258 "
for %%e in (_internal\_tcl_data\encoding\*.enc) do (
    echo "%KEEPENC%" | findstr /i /c:" %%~ne " >nul || del "%%e"
)

rem The C++ libraries that come with Vosk carry their debugging information (21 MB of libstdc++'s 25 MB). strip takes
rem out only that: the parts Windows loads stay byte for byte the same. Without a strip.exe they're left as they are
set "STRIP="
for %%s in (strip.exe) do set "STRIP=%%~$PATH:s"
if not defined STRIP if exist "%ProgramFiles(x86)%\Dev-Cpp\MinGW64\bin\strip.exe" set "STRIP=%ProgramFiles(x86)%\Dev-Cpp\MinGW64\bin\strip.exe"
if defined STRIP (
    for %%f in (libstdc++-6.dll libgcc_s_seh-1.dll libwinpthread-1.dll) do "%STRIP%" --strip-debug "_internal\vosk\%%f" >nul 2>&1
) else (
    echo strip.exe wasn't found, so Vosk's libraries keep their debugging information, about 21 MB
)
rmdir /s /q dist build model_build
echo Built %~dp0LettucePlayer.exe (keep the _internal folder beside it)
