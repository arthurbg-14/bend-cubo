#!/usr/bin/env python3
# Rasterizes Liberation Mono into 8x16 cells for Latin-1 32..255 and
# prints the GLSL table the HUD reads (effs/font.glsl): a glyph is 4
# words, word j holding rows 4j..4j+3, a byte a row, bit 7 the left.
import sys
from PIL import Image, ImageDraw, ImageFont
path = "/usr/share/fonts/liberation/LiberationMono-Regular.ttf"
font = ImageFont.truetype(path, 13)
words = []
for c in range(32, 256):
    ch = chr(c)
    img = Image.new("L", (8, 16), 0)
    d = ImageDraw.Draw(img)
    if 127 <= c < 160:
        ch = " "
    d.text((0, 1), ch, fill=255, font=font)
    rows = []
    for y in range(16):
        b = 0
        for x in range(8):
            if img.getpixel((x, y)) >= 110:
                b |= 1 << (7 - x)
        rows.append(b)
    for j in range(4):
        w = rows[4*j] | rows[4*j+1] << 8 | rows[4*j+2] << 16 | rows[4*j+3] << 24
        words.append(w)
out = ["// Liberation Mono, 8x16, Latin-1 32..255 (tools/font.py)",
       "const uint FONT[%d] = uint[](" % len(words)]
for i in range(0, len(words), 8):
    out.append("  " + ", ".join("0x%08xu" % w for w in words[i:i+8]) + ("," if i + 8 < len(words) else ""))
out.append(");")
print("\n".join(out))
if len(sys.argv) > 1:
    # preview a string
    s = sys.argv[1]
    for y in range(16):
        line = ""
        for ch in s:
            g = ord(ch) - 32
            w = words[g*4 + y//4] >> (8*(y%4)) & 255
            line += "".join("#" if w >> (7-x) & 1 else "." for x in range(8))
        print(line, file=sys.stderr)
