#!/usr/bin/python3

import re, sys

def fix_file(filename):
    fixed = []
    with open(filename,"r") as f:
        for line in f.readlines():
            line = re.sub("^(\s*)def\s+(\S*)\s*(?:==|\\\\<equiv>)\s*\"",r'\1define \2 where "\2 \\<equiv> ',line)
            fixed.append(line)
    with open(filename,"w") as f:
        for line in fixed:
            f.write(line)

fix_file(sys.argv[1])

