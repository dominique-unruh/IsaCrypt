#!/usr/bin/python

# sudo apt-get install python2-pyro4
# sudo pip install serpent

import glob, sys, os, random, re, subprocess, time
import unittest
import Pyro4

run_theory_ml = r"""
datatype thyexn = Theory | Exception of exn;;

fun run_theory thy_name thy_name_nopath stop =
  let (* val _ = writeln("Theory "^thy_name) *)
      val _ = Thy_Info.kill_thy thy_name_nopath
      val res = (Thy_Info.use_thy (thy_name,Position.none); Theory)
                     handle e => Exception e
  in
    case res of
      Theory => ()
    | Exception e => writeln("\n*** EXCEPTION[[["^exnMessage e^"]]] ***");
    writeln("\n"^stop)
  end;;

val _ = writeln "\n*** INITIALIZATION FINISHED ***";;
""";


log_file = os.environ['HOME']+"/tmp/isabelle-tests.log"
class IsabelleProcess(object):
    def __init__(self):
        self.log_file_handle = open(log_file,"w")
        self.isabelle_proc = None
        
    def log(self,msg):
        self.log_file_handle.write(msg+"\n")
        self.log_file_handle.flush()

    def start_isabelle_proc(self):
        if self.isabelle_proc!=None: return
        logic = "HOL"
        cmd = ['/opt/Isabelle/bin/isabelle_process', '-o', 'quick_and_dirty=true', logic, '-q']
        self.isabelle_proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stdin=subprocess.PIPE)
        self.communicate_until(run_theory_ml,"*** INITIALIZATION FINISHED ***");

    def communicate_until(self,input,stop):
        self.start_isabelle_proc()
        assert input[-1]=="\n"
        self.log("Sending (stop={}): {}".format(stop,input))
        self.isabelle_proc.stdin.write(input)
        self.isabelle_proc.stdin.flush()
        out = []
        while True:
            l=self.isabelle_proc.stdout.readline()
            assert l!=""
            self.log("Received: "+l.strip('\r\n'))
            out.append(l)
            if l.strip('\r\n')==stop: self.log("(Stopword)"); break
        return "".join(out)
        
    def check(self):
        self.start_isabelle_proc()
        if self.isabelle_proc.poll()!=None:
            self.log("*** Isabelle process died. Exiting server. ***")
            exit(1)
            
    def shutdown(self):
        if self.isabelle_proc and self.isabelle_proc.poll()==None:
            self.isabelle_proc.terminate()
            time.sleep(1)
            self.isabelle_proc.kill()
        exit(0)


def run_theory(thy):
    server=get_server()
    server.log("Testing "+thy)
    info = parse_thy(thy)
    expect = info['expect']
    (thy_noext,ext) = os.path.splitext(thy)
    thy_nopath = os.path.split(thy_noext)[1]
    stop = str(random.randint(0,2**60))
    ml = 'val _ = run_theory "{thy}" "{thy_np}" "{stop}";;\n'.format(thy=thy_noext,thy_np=thy_nopath,stop=stop)
    
    # Running once to get all theories loaded (without having them clutter the output)
    server.communicate_until(ml,stop)
    out = server.communicate_until(ml,stop)

    err=[]
    def set_err(e): err.append(e.group(0)); ""
    out = re.sub(r"\*\*\* EXCEPTION\[\[\[(.*)\]\]\] \*\*\*",set_err,out)
    out = re.sub(r"^\s*ML>\s*","",out)
    out = re.sub(r'^\s*Theory loader: removing "[^"]*\s*"',"",out)
    out = re.sub(r'^\s*Loading theory "[^"]*"\s*',"",out)
    out = re.sub(stop+r"\s*$","",out)
    out = re.sub(r"val it = \(\): unit\s*$","",out)
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

def start_server():
    # TODO: check options, in particular for security (local access only)
    daemon = Pyro4.Daemon()
    server = IsabelleProcess()
    server.uri=daemon.register(server)
    with open(".isabelle_test_server","w") as f: f.write(str(server.uri))
    daemon.requestLoop()

def shutdown_server():
    uri=open(".isabelle_test_server","r").read()
    isabelle_server=Pyro4.Proxy(uri)
    isabelle_server.shutdown()

isabelle_server=None
def get_server():
    global isabelle_server
    def connect():
        global isabelle_server
        uri=open(".isabelle_test_server","r").read()
        isabelle_server=Pyro4.Proxy(uri)
        isabelle_server.check()
    def start():
        print "Starting server..."
        os.system("nohup python tests.py ISABELLE_SERVER >.isabelle-server-out.log 2>&1 &")
        time.sleep(1)
        connect()

    if isabelle_server!=None: 
        isabelle_server.check()
        return isabelle_server
    try: connect()
    except IOError: start()
    except Pyro4.errors.CommunicationError: start()

    return isabelle_server
    

if __name__ == "__main__":
    if len(sys.argv)>1 and sys.argv[1]=="ISABELLE_SERVER":
        start_server()
    if len(sys.argv)>1 and sys.argv[1]=="ISABELLE_SERVER_SHUTDOWN":
        shutdown_server()
    else:
        discover_tests()
