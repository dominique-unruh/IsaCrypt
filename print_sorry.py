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

    subprocess.check_call("/opt/Isabelle/bin/isabelle build -d . -v HOL-EC-Print-Sorry",shell=True)

    with gzip.open("/home/unruh/.isabelle/Isabelle2014/heaps/polyml-5.5.2_x86-linux/log/HOL-EC-Print-Sorry.gz",'rt') as log:
      with open("print_sorry_report.txt","wt") as out:
        show = False
        for line in log:
            line = str(line)
            if line[0]=='\x0c': continue
            if show: out.write(line)
            if line == "======== STARTING PRINT_SORRY ========\n": show = True

print_sorry(["Procs_Typed.reduce_procfun.seq","Procs_Typed.reduce_procfun.apply1"])
#print_sorry(["Scratch.test"])
