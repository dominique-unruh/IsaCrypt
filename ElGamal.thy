theory ElGamal
imports Hoare_Tactics Procs_Typed Scratch2 Tactic_Inline Lang_Simplifier
begin

default_sort prog_type

class ab_group_mult = inverse + ab_semigroup_mult + monoid_mult +
  assumes left_inverse [simp]: "(inverse a) * a = 1"

lemma (in ab_group_mult) right_inverse [simp]: "a * inverse a = 1"
  by (subst mult_commute, simp)

locale group =
  (* fixes 'G *)
  fixes g::"'G::{prog_type,inverse,power,ab_group_mult}" (* generator *) (* TODO: remove unneeded classes *)
  and q::nat (* group order *)


type_synonym 'g DDH_Adv = "('g*'g*'g*unit,bool) procedure"
type_synonym 'g DDH_Game = "(unit,bool) procedure"

definition_by_specification (in group) DDH0 :: "'G DDH_Adv =proc=> 'G DDH_Game" where
  "procfun_apply DDH0 A = 
    LOCAL x y b.
    proc () { 
      x <- uniform {0..<q};
      y <- uniform {0..<q};
      b := call A (g^x, g^y, g^(x*y));
      return True
    }"

definition_by_specification (in group) DDH1 :: "'G DDH_Adv =proc=> 'G DDH_Game" where
  "procfun_apply DDH1 A = 
    LOCAL x y z b.
    proc () {
      x <- uniform {0..<q};
      y <- uniform {0..<q};
      z <- uniform {0..<q};
      b := call A (g^x, g^y, g^z);
      return True
    }"

(* (keygen,enc,dec) *)
type_synonym ('pk,'sk,'m,'c) EncScheme = 
 "(unit,'pk*'sk) procedure *
  ('pk*'m*unit, 'c) procedure *
  ('sk*'c*unit, 'm option) procedure"

(* TODO: use this *)
(*record ('pk,'sk,'m,'c) EncScheme2 = 
 keygen :: "(unit,'pk*'sk) procedure"
 enc :: "('pk*'m*unit, 'c) procedure"
 dec :: "('sk*'c*unit, 'm option) procedure"*)


(* (choose,guess) *)
type_synonym ('pk,'sk,'m,'c) CPA_Adv = 
 "('pk*unit,'m*'m) procedure *
  ('c*unit,bool) procedure"

type_synonym CPA_Game = "(unit,bool)procedure"

definition_by_specification CPA_main :: "('pk,'sk,'m,'c) EncScheme * ('pk,'sk,'m,'c) CPA_Adv =proc=> CPA_Game" where
 "procfun_apply CPA_main ((kg,enc,dec),(Achoose,Aguess)) = 
  LOCAL pk sk m0 m1 b c b' tmp1 tmp2.
  proc () { 
    tmp1 := call kg();
    pk := fst tmp1;
    sk := snd tmp1;
    tmp2 := call Achoose(pk);
    m0 := fst tmp2;
    m1 := snd tmp2;
    b <- uniform UNIV;
    c := call enc(pk, if b then m1 else m0);
    b' := call Aguess(c);
    return b'=b
  }"

definition (in group) ElGamal :: "('G,nat,'G,'G\<times>'G) EncScheme" where
 "ElGamal = LOCAL pk m0 c sk sk' y gm gy.
   (proc() { sk <- uniform {0..<q}; return (g^sk, sk) },
    proc(pk,m0) { y <- uniform {0..<q}; return (g^y, pk^y * m0) },
    proc(sk',c) { gy := fst c; gm := snd c; return Some (gm * inverse (gy^sk')) })"

(*
module Correctness (S:Scheme) = {
  proc main(m:plaintext) : bool = {
    var pk : pkey;
    var sk : skey;
    var c  : ciphertext;
    var m' : plaintext option;

    (pk, sk) = S.kg();
    c        = S.enc(pk, m);
    m'       = S.dec(sk, c); 
    return (m' = Some m);
  }
}.
*)

lemma set_filter_empty: "Set.filter f {} = {}" by auto
lemma set_filter_union: "Set.filter f (x\<union>y) = Set.filter f x \<union> Set.filter f y" by auto
(*lemma HIDDEN_EQ_set_filter: "HIDDEN_EQ (set (vars_proc_global p)) x \<Longrightarrow> 
  HIDDEN_EQ (Set.filter (\<lambda>x\<Colon>variable_untyped. \<not> vu_global x) (set (vars_proc_global p))) x"
by (simp add: set_filter_vars_proc_global) *)
lemma HIDDEN_EQ_set_filter: "HIDDEN_EQ (Set.filter (\<lambda>x\<Colon>variable_untyped. \<not> vu_global x) (set (vars_proc_global p))) {}"
  unfolding HIDDEN_EQ_def vars_proc_global_def by auto

definition_by_specification Correctness :: "(_,_,_,_) EncScheme =proc=> (_*unit,bool)procedure" where
  "procfun_apply Correctness (kg,enc,dec) = LOCAL m1 m2 succ pksk c1.
  proc(m1) {
    pksk := call kg();
    c1 := call enc(fst pksk, m1);
    m2 := call dec(snd pksk, c1);
    succ := (m2 = Some m1);
    return succ
  }"

lemma h1: "scheme = (fst scheme, fst (snd scheme), snd (snd scheme))" by auto

(* TODO: create those automatically *)
schematic_lemma Correctness_body [procedure_info]: "p_body (procfun_apply Correctness scheme) == ?b" 
  apply (subst h1) apply (rule HIDDEN_EQ_I') unfolding Correctness_def apply simp by (fact HIDDEN_EQ_refl)
schematic_lemma Correctness_return [procedure_info]: "p_return (procfun_apply Correctness scheme) == ?b" 
  apply (subst h1) apply (rule HIDDEN_EQ_I') unfolding Correctness_def apply simp by (fact HIDDEN_EQ_refl)
schematic_lemma Correctness_args [procedure_info]: "p_args (procfun_apply Correctness scheme) == ?b" 
  apply (subst h1) apply (rule HIDDEN_EQ_I') unfolding Correctness_def by (simp?, rule HIDDEN_EQ_procargs)+
schematic_lemma Correctness_body_vars [procedure_info]: "
  \<lbrakk> set (vars_proc_global (fst scheme)) == ?v1; set (vars_proc_global (fst(snd scheme))) == ?v2; set (vars_proc_global (snd(snd scheme))) == ?v3\<rbrakk>
  \<Longrightarrow> set (vars (p_body (procfun_apply Correctness scheme))) == ?b"
  apply (subst h1) apply (drule HIDDEN_EQ_D')+ apply (rule HIDDEN_EQ_I')
  unfolding Correctness_body apply simp_all by (rule HIDDEN_EQ_varset; simp?)+
schematic_lemma Correctness_return_vars [procedure_info]: "set (e_vars (p_return (procfun_apply Correctness scheme))) == ?b"
  apply (subst h1) apply (rule HIDDEN_EQ_I') unfolding Correctness_return by (simp?, rule HIDDEN_EQ_varset)+
schematic_lemma Correctness_body_local_vars [procedure_info]: "set (local_vars (p_body (procfun_apply Correctness scheme))) == ?b" 
  apply (subst h1) apply (rule HIDDEN_EQ_I')
  unfolding local_vars_def filter_set[symmetric] apply (subst Correctness_body_vars)
  unfolding filter_locals1 filter_locals2 filter_locals3 set_filter_empty set_filter_union
  apply simp_all by (rule HIDDEN_EQ_varset HIDDEN_EQ_set_filter; simp?)+




context group begin
schematic_lemma kg_body [procedure_info]: "p_body (fst ElGamal) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (fact HIDDEN_EQ_refl)
schematic_lemma kg_return [procedure_info]: "p_return (fst ElGamal) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (fact HIDDEN_EQ_refl)
schematic_lemma kg_args [procedure_info]: "p_args (fst ElGamal) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def by (simp, rule HIDDEN_EQ_procargs)+
schematic_lemma kg_body_vars [procedure_info]: "set (vars (p_body (fst ElGamal))) == ?b" apply (rule HIDDEN_EQ_I') unfolding kg_body ElGamal_def apply simp? by (rule HIDDEN_EQ_varset)+
schematic_lemma kg_return_vars [procedure_info]: "set (e_vars (p_return (fst ElGamal))) == ?b" apply (rule HIDDEN_EQ_I') unfolding kg_return ElGamal_def apply simp? by (rule HIDDEN_EQ_varset)+
schematic_lemma kg_body_local_vars [procedure_info]: "set (local_vars (p_body (fst ElGamal))) == ?b" 
 apply (rule HIDDEN_EQ_I')
 unfolding local_vars_def filter_set[symmetric] apply (subst kg_body_vars)
 unfolding filter_locals1 filter_locals2 filter_locals3 set_filter_empty
 by (rule HIDDEN_EQ_varset)+

schematic_lemma enc_args [procedure_info]: "p_args (fst (snd ElGamal)) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (rule HIDDEN_EQ_procargs)+
schematic_lemma enc_body_vars [procedure_info]: "set (vars (p_body (fst (snd ElGamal)))) == ?b" apply (rule HIDDEN_EQ_I') unfolding kg_body ElGamal_def apply simp? by (rule HIDDEN_EQ_varset)+
schematic_lemma enc_body_local_vars [procedure_info]: "set (local_vars (p_body (fst (snd ElGamal)))) == ?b" 
 apply (rule HIDDEN_EQ_I')
 unfolding local_vars_def filter_set[symmetric] apply (subst enc_body_vars)
 unfolding filter_locals1 filter_locals2 filter_locals3 set_filter_empty
 by (rule HIDDEN_EQ_varset)+
schematic_lemma enc_return_vars [procedure_info]: "set (e_vars (p_return (fst (snd ElGamal)))) == ?b" apply (rule HIDDEN_EQ_I') unfolding kg_return ElGamal_def apply simp? by (rule HIDDEN_EQ_varset)+
schematic_lemma enc_body [procedure_info]: "p_body (fst (snd ElGamal)) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (fact HIDDEN_EQ_refl)
schematic_lemma enc_return [procedure_info]: "p_return (fst (snd ElGamal)) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (fact HIDDEN_EQ_refl)

schematic_lemma dec_args [procedure_info]: "p_args (snd (snd ElGamal)) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (rule HIDDEN_EQ_procargs)+
schematic_lemma dec_body_vars [procedure_info]: "set (vars (p_body (snd (snd ElGamal)))) == ?b" apply (rule HIDDEN_EQ_I') unfolding kg_body ElGamal_def apply simp? by (rule HIDDEN_EQ_varset)+
schematic_lemma dec_body_local_vars [procedure_info]: "set (local_vars (p_body (snd (snd ElGamal)))) == ?b" 
 apply (rule HIDDEN_EQ_I')
 unfolding local_vars_def filter_set[symmetric] apply (subst dec_body_vars)
 unfolding filter_locals1 filter_locals2 filter_locals3 set_filter_empty
 by (rule HIDDEN_EQ_varset)+
schematic_lemma dec_return_vars [procedure_info]: "set (e_vars (p_return (snd (snd ElGamal)))) == ?b" apply (rule HIDDEN_EQ_I') unfolding kg_return ElGamal_def apply simp? by (rule HIDDEN_EQ_varset)+
schematic_lemma dec_body [procedure_info]: "p_body (snd (snd ElGamal)) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (fact HIDDEN_EQ_refl)
schematic_lemma dec_return [procedure_info]: "p_return (snd (snd ElGamal)) == ?b" apply (rule HIDDEN_EQ_I') unfolding ElGamal_def apply simp by (fact HIDDEN_EQ_refl)

end

lemma (in group) correctness:
  shows "LOCAL succ0. hoare {True} succ0 := call (procfun_apply Correctness ElGamal)(m) {succ0}"
apply (inline "procfun_apply Correctness ElGamal")
apply (inline "fst ElGamal")
apply (inline "snd (snd ElGamal)")
apply (inline "fst (snd ElGamal)")
apply (wp sample) apply skip apply auto
unfolding power_mult[symmetric] apply (subst mult.commute[where 'a=nat]) 
apply (subst mult.commute[where 'a='G]) apply (subst mult.assoc) by simp

lemma (in group) correctness0:
  defines "kg == fst ElGamal" and "enc == fst (snd ElGamal)" and "dec == snd (snd ElGamal)"
  shows "LOCAL pksk c0 m m'. 
         hoare {True} pksk := call kg();
                      c0 := call enc(fst pksk, $m);
                      m' := call dec(snd pksk, c0)
               {$m' = Some ($m)}"
using kg_def apply (inline "kg")
using dec_def apply (inline "dec")
using enc_def apply (inline "enc")
apply (wp sample) apply skip apply auto
unfolding power_mult[symmetric] apply (subst mult.commute[where 'a=nat]) 
apply (subst mult.commute[where 'a='G]) apply (subst mult.assoc) by simp

end
