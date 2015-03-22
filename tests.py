#!/usr/bin/python

import glob
import os
import random
import re
import subprocess
import unittest

log_file = os.environ['HOME']+"/tmp/isabelle-tests.log"
log_file_handle = None
def log(msg):
    global log_file, log_file_handle
    if log_file_handle==None:
        log_file_handle = open(log_file,"w")
    log_file_handle.write(msg+"\n")
    log_file_handle.flush()

def parse_thy(thy):
    content = open(thy).read()
    expect = []
    info = {}

    for m in re.finditer(r"^\s*\(\*\s+@([A-Za-z0-9_]+)(?:\s(.*))?\*\)\s*$",content,re.MULTILINE):
        (key,val) = m.groups()
        if val==None: val = ""
        val = val.strip()

        if key=="FAIL": expect.append(("FAIL",0))
        elif key=="SUITE": info['suite'] = val
        elif key=="OUTPUT_NOT": expect.append(("OUTPUT_NOT",val))
        elif key=="ERROR_NOT": expect.append(("ERROR_NOT",val))
        else: raise RuntimeError("Unknown key {} in {}".format(key,thy))

    if expect==[]: expect.append(("SUCCEED",0))
    info['expect'] = expect

    return info

# ignored_output = """> val commit = fn: unit -> unit
# val it = (): unit
# ML> Warning-Handler catches all exceptions.
# Found near
#   (Thy_Info.use_thy ("{thy}", Position.none); exit 0; ())
#   handle e => (writeln (exnMessage e); exit 1)
# """

run_theory_ml = r"""
datatype thyexn = Theory | Exception of exn;;

fun run_theory thy_name thy_name_nopath stop =
  let (* val _ = writeln("Theory "^thy_name) *)
      val res = (Thy_Info.use_thy (thy_name,Position.none); Theory)
                     handle e => Exception e
      val _ = Thy_Info.kill_thy thy_name_nopath
  in
    case res of
      Theory => ()
    | Exception e => writeln("\n*** EXCEPTION[[["^exnMessage e^"]]] ***");
    writeln("\n"^stop)
  end;;

val _ = writeln "\n*** INITIALIZATION FINISHED ***";;
""";

def communicate_until(proc,input,stop):
    assert input[-1]=="\n"
    log("Sending (stop={}): {}".format(stop,input))
    proc.stdin.write(input)
    proc.stdin.flush()
    out = []
    while True:
        l=proc.stdout.readline()
        assert l!=""
        log("Received: "+l.strip('\r\n'))
        out.append(l)
        if l.strip('\r\n')==stop: log("(Stopword)"); break
    return "".join(out)

isabelle_proc = None
def get_isabelle_proc():
    global isabelle_proc
    if isabelle_proc != None: return isabelle_proc 
    logic = "HOL"
    cmd = ['/opt/Isabelle/bin/isabelle_process', '-o', 'quick_and_dirty=true', logic, '-q']
    isabelle_proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stdin=subprocess.PIPE)
    communicate_until(isabelle_proc,run_theory_ml,"*** INITIALIZATION FINISHED ***");
    return isabelle_proc

def run_theory(thy):
    proc = get_isabelle_proc()
    log("Testing "+thy)
    info = parse_thy(thy)
    expect = info['expect']
    (thy_noext,ext) = os.path.splitext(thy)
    thy_nopath = os.path.split(thy_noext)[1]
    stop = str(random.randint(0,2**60))
    ml = 'val _ = run_theory "{thy}" "{thy_np}" "{stop}";;\n'.format(thy=thy_noext,thy_np=thy_nopath,stop=stop)
    
    # Running once to get all theories loaded (without having them clutter the output)
    communicate_until(proc,ml,stop)
    out = communicate_until(proc,ml,stop)

    #ignored_output2 = ignored_output.format(thy=thy_noext,thy_basename=os.path.basename(thy_noext))
    #if out.startswith(ignored_output2): out = out[len(ignored_output2):]
    #if out != "": print "\nOutput:\n"+out
    #if err != "": print "\nStderr:\n"+err
    
    err=[]
    def set_err(e): err.append(e.group(0)); ""
    out = re.sub(r"\*\*\* EXCEPTION\[\[\[(.*)\]\]\] \*\*\*",set_err,out)
    out = re.sub(r"^ML>\s+","",out)
    out = re.sub(r'^\s*Loading theory "[^"]*"',"",out)
    out = re.sub(stop+r"\s*$","",out)
    out = re.sub(r"val it = \(\): unit\s*$","",out)
    out = re.sub(r'Theory loader: removing "[^"]*"\s*$',"",out)
    out = out.strip()
    success = err==[]
    err = "".join(err)

    print "Success: {}".format(success)
    if out != "": print "\nOutput:\n"+out
    if err != "": print "\nError:\n"+err

    for (k,v) in expect:
        if k=="SUCCEED":
            assert success
        elif k=="FAIL":
            assert not success
        elif k=="OUTPUT_NOT":
            assert out.find(v)==-1
        elif k=="ERROR_NOT":
            assert err.find(v)==-1
        else:
            raise Exception("Undefined expect-keyword "+k)

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
