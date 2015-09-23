theory Scratch
imports Lang_Typed
begin

term "proc() { skip; return 1 }"
term "proc(a) { skip; return 1 }"
term "proc(a,b,c) { skip; return 1 }"
term "PROGRAM [ x := call f() ]"                        
term "PROGRAM [ (x,y) := call f(1) ]"
term "PROGRAM [ x := call f(1,2) ]"
term "PROGRAM [ x := y ]"
term "PROGRAM [ (x,y) := (1,2,3) ]"



end