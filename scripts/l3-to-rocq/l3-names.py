#!/usr/bin/env python3
"""Print the datatype names (in order) or the [_def] names of an
L3-generated HOL script (`<name>Script.sml` written by L3's Import).

  l3-names.py types SCRIPT     # Construct/Record type names, in order
  l3-names.py defs SCRIPT      # `val <name>_def = Def...` names, in order
"""
import re
import sys

mode, path = sys.argv[1], sys.argv[2]
s = open(path).read()
if mode == "defs":
    for m in re.finditer(r"^val ([A-Za-z0-9_']*_def) = ", s, re.M):
        print(m.group(1))
elif mode == "types":
    for m in re.finditer(r"val _ = (Record|Construct)\s*", s):
        i = m.end()
        if m.group(1) == "Record":
            print(re.match(r'\s*\(\s*"([^"]+)"', s[i:]).group(1))
            continue
        k = s.index("[", i)
        d = 0
        while True:
            c = s[k]
            if c in "([":
                d += 1
            elif c in ")]":
                d -= 1
            if d == 0:
                break
            if c == "(" and d == 2:
                print(re.match(r'\(\s*"([^"]+)"', s[k:]).group(1))
            k += 1
else:
    sys.exit(__doc__)
