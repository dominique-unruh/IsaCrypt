(* @SUITE modules *)

theory "moduletype"
imports "../Modules"
begin

declare[[show_types,show_sorts]]
moduletype MT1 where
  f1 :: "(int*unit,string) procedure"
and f2 :: "(bool*unit,real) procedure"

print_theorems


(* Checking constants *)
term "MT1::module_type"
term "MT1.f1 :: module \<Rightarrow> (int*unit,string) procedure"
term "MT1.f2 :: module \<Rightarrow> (bool*unit,real) procedure"

(* Checking lemmas *)
lemma "has_module_type (M\<Colon>module) MT1 \<Longrightarrow>
    get_proc_in_module M [''f1''] =
    Some (mk_procedure_untyped (MT1.f1 M))"
    by (rule MT1.f1)

lemma "has_module_type (M\<Colon>module) MT1 \<Longrightarrow>
    get_proc_in_module M [''f2''] =
    Some (mk_procedure_untyped (MT1.f2 M))"
    by (rule MT1.f2)



moduletype MT2(M1:MT1) where
  g1 :: "(int*unit,string) procedure"
and g2 :: "(bool*unit,real) procedure"

print_theorems

term "MT2::module_type"
(* TODO: getters *)

(* TODO: check getter lemmas *)

end
