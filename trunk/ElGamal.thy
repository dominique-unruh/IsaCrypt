theory ElGamal
imports Hoare_Tactics Procs_Typed Scratch2
begin

default_sort prog_type

locale group =
  (* fixes 'G *)
  fixes g::"'G::{prog_type,inverse,power,prog_type}" (* generator *)
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
 "ElGamal = LOCAL pk m c sk y gm gy.
   (proc() { sk <- uniform {0..<q}; return (g^sk, sk) },
    proc(pk,m) { y <- uniform {0..<q}; return (g^y, pk^y * m) },
    proc(sk,c) { gm := fst c; gy := snd c; return Some (gm * inverse gy^sk) })"

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

definition_by_specification Correctness :: "(_,_,_,_) EncScheme =proc=> (_*unit,bool)procedure" where
  "procfun_apply Correctness (kg,enc,dec) = LOCAL m m' succ pksk c.
  proc(m) {
    pksk := call kg();
    c := call enc(fst pksk, m);
    m' := call dec(snd pksk, c);
    succ := (m' = Some m);
    return succ
  }"

definition "HIDDEN_EQ = op="
lemma HIDDEN_EQ_refl: "HIDDEN_EQ x x" unfolding HIDDEN_EQ_def ..
lemma HIDDEN_EQ_procargs:
  shows "HIDDEN_EQ procargvars_empty procargvars_empty"
    and "HIDDEN_EQ a b \<Longrightarrow> HIDDEN_EQ (procargvars_add (LVariable x) a) (procargvars_add (LVariable x) b)"
unfolding HIDDEN_EQ_def by auto
lemma HIDDEN_EQ_varset:
  fixes x x'
  defines "x == mk_variable_untyped (LVariable x')"
  shows "HIDDEN_EQ {} {}"
    and "HIDDEN_EQ a b \<Longrightarrow> HIDDEN_EQ (Set.insert x a) (Set.insert x b)"
unfolding HIDDEN_EQ_def by auto

context group begin
(* TODO: should not be necessary *)
definition "kg == fst ElGamal"
schematic_lemma kg_body: "p_body kg = ?b" unfolding HIDDEN_EQ_def[symmetric] unfolding kg_def ElGamal_def apply simp by (fact HIDDEN_EQ_refl)
schematic_lemma kg_return: "p_return kg = ?b" unfolding HIDDEN_EQ_def[symmetric] unfolding kg_def ElGamal_def apply simp by (fact HIDDEN_EQ_refl)
schematic_lemma kg_args: "p_args kg = ?b" unfolding HIDDEN_EQ_def[symmetric] unfolding kg_def ElGamal_def by (simp, rule HIDDEN_EQ_procargs)+
schematic_lemma kg_body_vars: "set (vars (p_body kg)) = ?b" unfolding HIDDEN_EQ_def[symmetric] unfolding kg_body ElGamal_def apply simp? by (rule HIDDEN_EQ_varset)+
schematic_lemma kg_return_vars: "set (e_vars (p_return kg)) = ?b" unfolding HIDDEN_EQ_def[symmetric] unfolding kg_return ElGamal_def apply simp? by (rule HIDDEN_EQ_varset)+
end

ML {*
val testtac = SUBGOAL (fn (goal,i) => raise ERROR("bla"))
*}

lemma (in group) correctness0:
  defines (*"kg == fst ElGamal" and*) "enc == fst (snd ElGamal)" and "dec == snd (snd ElGamal)"
  shows "LOCAL pksk c m m'. 
         hoare {True} pksk := call kg();
                      c := call enc(fst pksk, $m);
                      m' := call dec(snd pksk, c)
               {$m' = Some ($m)}"
apply (tactic \<open>inline_tac @{context} @{term kg} 1\<close>)
SORRY (* TODO: prove. First step: inline *)

lemma (in group) correctness:
  shows "hoare {True} succ := call (procfun_apply Correctness ElGamal)(m) {succ}"
unfolding ElGamal_def Correctness_def
SORRY (* TODO: prove. First step: inline *)

end
