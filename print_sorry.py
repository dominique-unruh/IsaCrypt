#!/usr/bin/python3

import subprocess, gzip

def print_sorry(thms):
    thys = " ".join(thm[:thm.find('.')] for thm in thms)
    with open("Tmp_Print_Sorry.thy","w") as f:
        f.write('''theory Tmp_Print_Sorry
        imports Extended_Sorry {thys}
begin
ML {{* writeln "======== STARTING PRINT_SORRY ========" *}}
'''.format(thys=thys))
        for thm in thms:
            f.write("""ML {{* writeln "==== {thm} ===" *}}
print_sorry {thm}

""".format(thm=thm));
        f.write("\nend\n")

    #subprocess.check_call("/opt/Isabelle/bin/isabelle build -d . -v HOL-EC-Print-Sorry",shell=True)

    with gzip.open("/home/unruh/.isabelle/Isabelle2014/heaps/polyml-5.5.2_x86-linux/log/HOL-EC-Print-Sorry.gz",'rt') as f:
        for line in f:
            line = str(line)
            if line[0]=='\x0c': continue
            line = line.rstrip("\r\n")
            print(line)

print_sorry(["Procs_Typed.reduce_procfun.seq","Procs_Typed.reduce_procfun.apply1"])
