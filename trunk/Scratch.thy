theory Scratch
imports Lang_Typed
begin

syntax "_xxx" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c" (binder "XXX" 3)
print_syntax

term "PROGRAM[ local x; x := x ]"

end
