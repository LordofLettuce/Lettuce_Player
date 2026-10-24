"""Writes the speech model's word list (Kaldi's words.txt) out of its language model, graph/Gr.fst.

The app always gives Vosk its own list of phrases (song names and commands), and with such a list Vosk builds its own
small language model: the model's general one, Gr.fst (24 MB), is never used. Vosk only needs the words in it, which it
reads from words.txt when Gr.fst isn't there. build.bat runs this on a copy of the model and leaves Gr.fst out.

    python vosk_words.py <model>/graph/Gr.fst <model>/graph/words.txt
"""
import struct
import sys

FST_MAGIC, SYMBOLS_MAGIC = 2125659606, 2125658996 # how an OpenFst file, and a symbol table inside one, begin
HAS_INPUT_SYMBOLS = 1


def main(fstPath, wordsPath):
    data = open(fstPath, "rb").read()
    at = 0

    def take(fmt):
        nonlocal at
        value = struct.unpack_from(fmt, data, at)[0]
        at += struct.calcsize(fmt)
        return value

    def text():
        nonlocal at
        length = take("<i")
        value = data[at:at + length].decode("utf-8")
        at += length
        return value

    if take("<i") != FST_MAGIC:
        sys.exit(f"{fstPath} isn't an OpenFst file")
    text(), text() # the FST's type and its arc type
    take("<i") # version
    flags = take("<i")
    take("<Q"), take("<q"), take("<q"), take("<q") # properties, start state, number of states, number of arcs
    if not flags & HAS_INPUT_SYMBOLS or take("<i") != SYMBOLS_MAGIC:
        sys.exit(f"{fstPath} has no word list in it")
    text(), take("<q") # the table's name, its next free key
    count = take("<q")
    with open(wordsPath, "w", encoding="utf-8", newline="\n") as out:
        for _ in range(count):
            word = text()
            out.write(f"{word} {take('<q')}\n")
    print(f"{count} words written to {wordsPath}")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    main(sys.argv[1], sys.argv[2])
