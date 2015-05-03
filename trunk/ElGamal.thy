theory ElGamal
imports Hoare_Tactics Procs_Typed
begin

definition "module_type_type (Rep::'a::type\<Rightarrow>'b::procedure_functor) = 
    (\<lambda>x::'a itself. procedure_functor_type TYPE('b))"
definition "module_type_mk_untyped (Rep::'a::type\<Rightarrow>'b::procedure_functor) = 
    (\<lambda>x::'a. procedure_functor_mk_untyped (Rep x))"
definition "module_type_mk_typed' (Rep::'a::type\<Rightarrow>'b::procedure_functor) = 
  (\<lambda>x. inv Rep (procedure_functor_mk_typed x))"

record 'G DDH_Adv =
  "guess" :: "('G*'G*'G*unit,bool) procedure"
term Rep_DDH_Adv_ext

class singleton_procedure_functor = singleton + procedure_functor
instantiation unit :: procedure_functor begin
  definition "procedure_functor_type (_::unit itself) == undefined::procedure_type_open"
  definition "procedure_functor_mk_untyped (_::unit) == undefined::procedure_rep"
  definition "procedure_functor_mk_typed' (_::procedure_rep) == ()"
  instance SORRY "this is wrong, currently"
end

(*
lemma module_type_OFCLASS:
  fixes Rep :: "'a::type \<Rightarrow> 'b::procedure_functor"
  assumes "procedure_functor_type = module_type_type Rep"
  assumes "procedure_functor_mk_untyped = module_type_mk_untyped Rep"
  assumes "procedure_functor_mk_typed' = module_type_mk_typed' Rep"
  shows "OFCLASS('a::type, procedure_functor_class)"
apply intro_classes
*)

instantiation DDH_Adv_ext :: (prog_type,singleton_procedure_functor)procedure_functor begin
  abbreviation "Rep == Rep_DDH_Adv_ext :: ('a,'b) DDH_Adv_ext \<Rightarrow> _"
  lemma inv_Rep: "inv Rep == Abs_DDH_Adv_ext"
    by (smt2 Abs_DDH_Adv_ext_inverse Rep_DDH_Adv_ext_inverse UNIV_I inv_equality)
  definition "procedure_functor_type = module_type_type Rep"
  definition "procedure_functor_mk_untyped = module_type_mk_untyped Rep"
  definition "procedure_functor_mk_typed' = module_type_mk_typed' Rep"
  instance apply intro_classes
    apply (metis (mono_tags) module_type_mk_untyped_def module_type_type_def procedure_functor_mk_untyped_DDH_Adv_ext_def procedure_functor_type_DDH_Adv_ext_def procedure_functor_welltyped)
    apply (metis (mono_tags) Abs_DDH_Adv_ext_cases Abs_DDH_Adv_ext_inverse UNIV_I module_type_mk_untyped_def procedure_functor_beta_reduced procedure_functor_mk_untyped_DDH_Adv_ext_def)
    unfolding procedure_functor_mk_untyped_DDH_Adv_ext_def procedure_functor_mk_typed'_DDH_Adv_ext_def
      module_type_mk_untyped_def module_type_mk_typed'_def inv_Rep
    apply (metis (mono_tags) Abs_DDH_Adv_ext_inverse UNIV_I beta_reduced_beta_reduce_id module_type_type_def procedure_functor_mk_typed_inverse procedure_functor_type_DDH_Adv_ext_def)
    by (metis Rep_DDH_Adv_ext_inverse procedure_functor_mk_untyped_inverse)
end 

type_synonym 'G DDH_Game = "('G*'G*'G*unit,bool) procedure"

locale group =
  (* fixes 'G *)
  fixes g::"'G::{prog_type,power}" (* generator *)
  and q::nat (* group order *)
begin

end

abbreviation "x == LVariable ''x'' :: nat variable"
abbreviation "y == LVariable ''y'' :: nat variable "
abbreviation "z == LVariable ''z'' :: nat variable"
abbreviation "b == LVariable ''b'' :: bool variable"
abbreviation "pk == LVariable ''pk'' :: 'pk variable"
abbreviation "sk == LVariable ''sk'' :: 'sk variable"
abbreviation "m0 == LVariable ''m0'' :: 'm variable"
abbreviation "m1 == LVariable ''m1'' :: 'm variable"
abbreviation "b' == LVariable ''b_'' :: bool variable"
abbreviation "tmp == LVariable ''tmp''"

(*
record Adversary =
  Adv_guess :: "(G*G*G*unit,bool) procedure"

record DDH_Game =
  DDH_main :: "(unit,bool) procedure"
*)

(* Hack for typechecking to go through *)
definition (in group) "A_guess == undefined ::  ('G \<times> 'G \<times> 'G \<times> unit, bool) procedure"

definition (in group) "DDH0_main = 
  proc () {
    x <- uniform {0..<q};
    y <- uniform {0..<q};
    b := call A_guess (g^x, g^y, g^(x*y));
    return True
  }"

definition (in group) DDH0 :: module where
"DDH0 == Abs_module \<lparr> mr_module_args=[''A'' \<mapsto> DDH_Adv],
                   mr_procs=[[''main''] \<mapsto> mk_procedure_untyped DDH0_main] \<rparr>"

definition (in group) "DDH1_main = 
  proc () {
    x <- uniform {0..<q};
    y <- uniform {0..<q};
    z <- uniform {0..<q}; 
    b := call A_guess (g^x, g^y, g^z);
    return True 
  }"

definition (in group) DDH1 :: module where
"DDH1 == Abs_module \<lparr> mr_module_args=[''A'' \<mapsto> DDH_Adv],
                   mr_procs=[[''main''] \<mapsto> mk_procedure_untyped DDH1_main] \<rparr>"


locale encscheme =
  fixes stone :: "('pk::prog_type*'sk::prog_type*'m::prog_type*'c::prog_type)itself"
begin

moduletype EncScheme attach stone where
    kg :: "(unit,'pk*'sk) procedure"
and enc :: "('pk*'m*unit, 'c::prog_type) procedure"
and dec :: "('sk*'c::prog_type*unit, 'm) procedure"

moduletype CPA_Adv(S:EncScheme) where
     choose :: "('pk*unit,'m*'m) procedure"
and "guess" :: "('c*unit,bool) procedure"

end

term encscheme.EncScheme

(* Hack for typechecking to go through *)
definition (in encscheme) "A_choose == undefined :: ('pk*unit,'m*'m) procedure"
definition (in encscheme) "A_guess == undefined :: ('c*unit,bool) procedure"
definition (in encscheme) "S_kg == undefined :: (unit,'pk*'sk)procedure"
definition (in encscheme) "S_enc == undefined :: ('pk*'m*unit,'c)procedure"

abbreviation "c == LVariable ''c'' :: 'c variable"

definition (in encscheme) 
 "CPA_main = ignore stone (proc () { 
    tmp := call S_kg();
    pk := fst (tmp::'pk*'sk);
    sk := snd (tmp::'pk*'sk);
    tmp := call A_choose(pk);
    m0 := fst (tmp::'m*'m);
    m1 := snd (tmp::'m*'m);
    b <- uniform UNIV;
    c := call S_enc(pk, if b then m1 else m0);
    b' := call A_guess(c);
    return (b'=b)
  })"

definition (in encscheme) CPA :: module where
"CPA == ignore stone (Abs_module \<lparr> mr_module_args=[''A'' \<mapsto> CPA_Adv, ''S'' \<mapsto> EncScheme],
                   mr_procs=[[''main''] \<mapsto> mk_procedure_untyped CPA_main] \<rparr>)"

end
