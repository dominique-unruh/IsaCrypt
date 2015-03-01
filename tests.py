#!/usr/bin/python

import subprocess
import unittest

def run_theory(thy):
    ml = '(Thy_Info.use_thy ("{thy}",Position.none); exit 0) handle e => (writeln (exnMessage e); exit 1);;'.format(thy=thy)
    cmd = ['/opt/Isabelle/bin/isabelle_process', 'EasyCrypt', '-q']
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stdin=subprocess.PIPE, stderr=subprocess.PIPE)
    (out, err) = proc.communicate(input=ml)
    return (proc.returncode,out,err)


class WP_IF(unittest.TestCase):
    def runTest(self):
        (ret,out,err) = run_theory('tests/wp_if')
        assert ret == 0

class Fail(unittest.TestCase):
    def runTest(self):
        (ret,out,err) = run_theory('tests/fail')
        assert ret != 0

if __name__ == "__main__":
    unittest.main()
