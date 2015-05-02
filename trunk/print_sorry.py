#!/usr/bin/python3

import subprocess

def print_sorry(thms):
    thys = " ".join(thm[:thm.find('.')] for thm in thms)
    with open("Tmp_Print_Sorry.thy","w") as f:
        f.write('''theory Tmp_Print_Sorry
        imports "~~/src/HOL/Proofs" Extended_Sorry {thys}
begin
'''.format(thys=thys)
        for thm in thms:
            f.write("""print_sorry {thm}

""".format(thm=thm));
        f.write("\nend\n")

    subprocess.check_call("""/opt/Isabelle/bin/isabelle_process -q -o quick_and_dirty=true -e 'proofs := 2; Thy_Info.use_thy ("Tmp_Print_Sorry",Position.none); exit(0);' HOL-EC-Prereqs </dev/null >print_sorry_raw.log""",shell=True)


print_sorry(["Procs_Typed.reduce_procfun.apply1"])
#print_sorry("Scratch","test")
