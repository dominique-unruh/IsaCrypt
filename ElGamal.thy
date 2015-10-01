theory ElGamal
imports Hoare_Tactics Procs_Typed Tactic_Inline Lang_Simplifier
begin

subsection {* General setup *}

default_sort prog_type

class ab_group_mult = inverse + ab_semigroup_mult + monoid_mult +
  assumes left_inverse [simp]: "(inverse a) * a = 1"

lemma (in ab_group_mult) right_inverse [simp]: "a * inverse a = 1"
  by (subst mult_commute, simp)

locale group =
  (* fixes 'G *)
  fixes g::"'G::{prog_type,inverse,power,ab_group_mult}" (* generator *)
  and q::nat (* group order *)

subsection {* DDH *}

type_synonym 'g DDH_Adv = "('g*'g*'g,bool) procedure"
type_synonym 'g DDH_Game = "(unit,bool) procedure"

procedure (in group) DDH0 :: "'G DDH_Adv =proc=> 'G DDH_Game" where
  "DDH0 <$> A = 
    LOCAL x y b.
    proc () {
      x <- uniform {0..<q};
      y <- uniform {0..<q};
      b := call A (g^x, g^y, g^(x*y));
      return True
    }"

procedure (in group) DDH1 :: "'G DDH_Adv =proc=> 'G DDH_Game" where
  "DDH1 <$> A = 
    LOCAL x y z b.
    proc () {
      x <- uniform {0..<q};
      y <- uniform {0..<q};
      z <- uniform {0..<q};
      b := call A (g^x, g^y, g^z);
      return True
    }"

subsection {* Declaring module type EncScheme *}


module_type ('pk,'sk,'m,'c) EncScheme =
  keygen :: "(unit,'pk*'sk) procedure"
  enc :: "('pk*'m, 'c) procedure"
  dec :: "('sk*'c, 'm option) procedure"


subsection {* Declaring CPA game *}

module_type ('pk,'sk,'m,'c) CPA_Adv =
  pick    :: "('pk,'m*'m) procedure"
  "guess" :: "('c,bool) procedure"

procedure CPA_main :: "('pk,'sk,'m,'c) EncScheme * ('pk,'sk,'m,'c) CPA_Adv =proc=> (unit,bool)procedure" where
 "CPA_main <$> (E,A) = 
  LOCAL pk sk m0 m1 b c b' tmp1 tmp2.
  proc () {
    (pk,sk) := call keygen<$>E ();
    (m0,m1) := call pick<$>A (pk);
    b <- uniform UNIV;
    c := call enc<$>E(pk, if b then m1 else m0);
    b' := call guess<$>A (c);
    return b'=b
  }"

subsection {* ElGamal *}

definition (in group) ElGamal :: "('G,nat,'G,'G\<times>'G) EncScheme" where
 "ElGamal = LOCAL pk m0 c1 c2 sk sk' y gm gy.
   Abs_EncScheme (proc() { sk <- uniform {0..<q}; return (g^sk, sk) },
                  proc(pk,m0) { y <- uniform {0..<q}; return (g^y, pk^y * m0) },
                  proc(sk',(c1,c2)) { gy := c1; gm := c2; return Some (gm * inverse (gy^sk')) })"


procedure Correctness :: "(_,_,_,_) EncScheme =proc=> (_,bool)procedure" where
  "Correctness <$> E = LOCAL m1 m2 succ pk0 sk0 c1.
  proc(m1) {
    (pk0,sk0) := call keygen<$>E ();
    c1 := call enc<$>E (pk0, m1);
    m2 := call dec<$>E (sk0, c1);
    succ := (m2 = Some m1);
    return succ
  }"


local_setup {* Procs_Typed.register_procedure_thm @{thm Correctness_def} *}

context group begin

schematic_lemma keygen_def': "keygen<$>ElGamal = ?x"
  unfolding ElGamal_def by simp
local_setup {* Procs_Typed.register_procedure_thm @{thm keygen_def'} *}


schematic_lemma enc_def': "enc<$>ElGamal = ?x"
  unfolding ElGamal_def by simp
local_setup {* Procs_Typed.register_procedure_thm @{thm enc_def'} *}

schematic_lemma dec_def': "dec<$>ElGamal = ?x"
  unfolding ElGamal_def by simp
local_setup {* Procs_Typed.register_procedure_thm @{thm dec_def'} *}

ML {* 
Procs_Typed.get_procedure_info @{context} true @{term "Correctness<$>ElGamal"}
*}

find_theorems "(p_vars (variable_pattern (_)))"

(* TODO move *)
lemma mk_expression_untyped_const_expression:
  "mk_expression_untyped (const_expression (x::'a)) = const_expression_untyped (Type TYPE('a)) (embedding x)"
  unfolding const_expression_def const_expression_untyped_def mk_expression_untyped_def e_fun_def e_vars_def
  by (subst Abs_expression_inverse, auto?)+

definition "assign_default_typed_rev vs = assign_default_typed (rev vs)"
lemma assign_default_typed_rev: "assign_default_typed vs = assign_default_typed_rev (rev vs)"
unfolding assign_default_typed_rev_def by auto

lemma "assign_default_typed ([mk_variable_untyped a,mk_variable_untyped b,mk_variable_untyped c]) =
  PROGRAM [ skip; a:=default; b:=default; c:=default ]"
  unfolding assign_default_typed_def assign_default_def program_def seq_def assign_def
      variable_pattern_def mk_expression_untyped_const_expression 
  apply (subst Abs_program_inverse, tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  apply (subst Abs_pattern_inverse, tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  by simp

lemma assign_default_typed_rev_cons: "assign_default_typed_rev (mk_variable_untyped v # vs) = seq (assign_default_typed_rev vs) (assign (variable_pattern v) (const_expression default))"
  unfolding assign_default_typed_def assign_default_typed_rev_def assign_default_def seq_def
    assign_def variable_pattern_def mk_expression_untyped_const_expression
  apply simp
  apply (subst Abs_program_inverse)
   using assign_default_def assign_default_welltyped close auto
  apply (subst Abs_program_inverse)
   close (simp add: embedding_Type eu_type_const_expression_untyped)
  apply (subst Abs_pattern_inverse)
   by auto

lemma assign_default_typed_rev_nil: "assign_default_typed_rev [] = Lang_Typed.skip"
  unfolding assign_default_typed_def assign_default_typed_rev_def assign_default_def skip_def
  by auto

lemma correctness:
  shows "LOCAL succ0. hoare {True} succ0 := call Correctness <$> ElGamal(m) {succ0}"
apply (inline "Correctness<$>ElGamal")
(* TODO remove *) apply (simp add: assign_default_typed_rev assign_default_typed_rev_cons assign_default_typed_rev_nil)
apply (inline "keygen<$>ElGamal")
(* TODO remove *) apply (simp add: assign_default_typed_rev assign_default_typed_rev_cons assign_default_typed_rev_nil)
apply (inline "dec<$>ElGamal")
apply (inline "enc<$>ElGamal")
apply (wp sample) apply skip apply autox
unfolding power_mult[symmetric] apply (subst mult.commute[where 'a=nat]) 
apply (subst mult.commute[where 'a='G]) apply (subst mult.assoc) by simp

end (* context: group *)




end (* theory *)
