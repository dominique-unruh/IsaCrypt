#!/usr/bin/python

import subprocess
import unittest
import glob
import os
import re

def run_theory(thy):
    content = open(thy).read()
    expect = []

    for m in re.finditer(r"^\s*\(\*\s+@([A-Z]+)(?:\s(.*))?\*\)",content):
        (key,val) = m.groups()
        if val==None: val = ""
        val = val.strip()

        if key=="FAIL": expect.append(("FAIL",0))
        else: raise RuntimeError("Unknown key {} in {}".format(key,thy))

    if expect==[]: expect.append(("SUCCEED",0))

    (thy_noext,ext) = os.path.splitext(thy)
    ml = '(Thy_Info.use_thy ("{thy}",Position.none); exit 0) handle e => (writeln (exnMessage e); exit 1);;'.format(thy=thy_noext)
    cmd = ['/opt/Isabelle/bin/isabelle_process', 'EasyCrypt', '-q']
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stdin=subprocess.PIPE, stderr=subprocess.PIPE)
    (out, err) = proc.communicate(input=ml)
    ret = proc.returncode

    print "Return value: {}".format(ret)
    if out != "": print "Output:\n"+out
    if err != "": print "Stderr:\n"+err

    for (k,v) in expect:
        if k=="SUCCEED":
            assert ret==0
        elif k=="FAIL":
            assert ret!=0

def discover_tests():
    global testsuite
    with open("testsuite.py","w") as f:
        f.write("""
import tests
import unittest

class Test(unittest.TestCase):
""")
        for thy in glob.glob("tests/*.thy"):
            (basename,ext) = os.path.splitext(os.path.basename(thy))
            f.write("    def test_{basename}(self): tests.run_theory('{thy}')\n".format(thy=thy,basename=basename))
        f.write("""
if __name__ == "__main__":
    unittest.main()
""")

if __name__ == "__main__":
    discover_tests()
