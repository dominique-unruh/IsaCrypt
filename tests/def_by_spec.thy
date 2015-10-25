(* @SUITE procs *)

theory def_by_spec
imports "../Procs_Typed"
begin

procedure p :: "(int,int)procedure" where
  "p = LOCAL a. proc(a) { skip; return a }"

procedure p' :: "(unit,unit)procedure \<Rightarrow> (int,int)procedure" where
  "p' q = LOCAL a x. proc(a) { x:=call q(); return a }"

end
