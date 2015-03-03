#!/usr/bin/python

import subprocess
import unittest
import glob
import os
import re

def parse_thy(thy):
    content = open(thy).read()
    expect = []
    info = {}

    for m in re.finditer(r"^\s*\(\*\s+@([A-Z]+)(?:\s(.*))?\*\)\s*$",content,re.MULTILINE):
        (key,val) = m.groups()
        if val==None: val = ""
        val = val.strip()

        if key=="FAIL": expect.append(("FAIL",0))
        elif key=="SUITE": info['suite'] = val
        else: raise RuntimeError("Unknown key {} in {}".format(key,thy))

    if expect==[]: expect.append(("SUCCEED",0))
    info['expect'] = expect

    return info

ignored_output = """> val commit = fn: unit -> unit
val it = (): unit
ML> Warning-Handler catches all exceptions.
Found near
  (Thy_Info.use_thy ("{thy}", Position.none); exit 0; ())
  handle e => (writeln (exnMessage e); exit 1)
"""

def run_theory(thy):
    info = parse_thy(thy)
    expect = info['expect']

    (thy_noext,ext) = os.path.splitext(thy)
    ml = '(Thy_Info.use_thy ("{thy}",Position.none); exit 0; ()) handle e => (writeln (exnMessage e); exit 1);;'.format(thy=thy_noext)
    cmd = ['/opt/Isabelle/bin/isabelle_process', 'EasyCrypt', '-q']
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stdin=subprocess.PIPE, stderr=subprocess.PIPE)
    (out, err) = proc.communicate(input=ml)
    ret = proc.returncode

    print "Return value: {}".format(ret)
    ignored_output2 = ignored_output.format(thy=thy_noext,thy_basename=os.path.basename(thy_noext))
    if out.startswith(ignored_output2): out = out[len(ignored_output2):]
    if out != "": print "\nOutput:\n"+out
    if err != "": print "\nStderr:\n"+err

    for (k,v) in expect:
        if k=="SUCCEED":
            assert ret==0
        elif k=="FAIL":
            assert ret!=0

def discover_tests():
    suites = {}
    for thy in glob.glob("tests/*.thy"):
        info = parse_thy(thy)
        suite = info.get('suite','Unsorted')
        if not suites.has_key(suite): suites[suite] = []
        suites[suite].append(thy)

    with open("testsuite.py","w") as f:
        f.write("""
import tests
import unittest
""")
        for suite in suites:
            f.write("""
class {}(unittest.TestCase):
""".format(suite))
            for thy in suites[suite]:
                (basename,ext) = os.path.splitext(os.path.basename(thy))
                f.write("    def test_{basename}(self): tests.run_theory('{thy}')\n".format(thy=thy,basename=basename))
        f.write("""
if __name__ == "__main__":
    unittest.main()
""")

if __name__ == "__main__":
    discover_tests()
