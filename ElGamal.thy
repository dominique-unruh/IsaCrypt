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
 "ElGamal = LOCAL pk m0 c1x c2x sk sk' y gm gy.
   Abs_EncScheme (proc() { sk <- uniform {0..<q}; return (g^sk, sk) },
                  proc(pk,m0) { y <- uniform {0..<q}; return (g^y, pk^y * m0) },
                  proc(sk',(c1x,c2x)) { gy := c1x; gm := c2x; return Some (gm * inverse (gy^sk')) })"


procedure Correctness :: "(_,_,_,_) EncScheme =proc=> (_,bool)procedure" where
  "Correctness <$> E = LOCAL m m2 succ pk sk c.
  proc(m) {
    (pk,sk) := call keygen<$>E ();
    c := call enc<$>E (pk, m);
    m2 := call dec<$>E (sk, c);
    succ := (m2 = Some m);
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

(* TODO move *)
lemma rename_local_variables_unit_pattern [simp]: "rename_local_variables_pattern ren unit_pattern = unit_pattern"
  by later

lemma rename_local_variables_variable_pattern [simp]: "rename_local_variables_pattern ren (variable_pattern v) = variable_pattern (rename_local_variables_var ren v)"
  by later

lemma rename_local_variables_sample [simp]: "rename_local_variables ren (sample x e) = sample (rename_local_variables_pattern ren x) (rename_local_variables_expression ren e)"
  by later

lemma rename_local_variables_apply_expression [simp]: "rename_local_variables_expression ren (apply_expression e v)
     = apply_expression (rename_local_variables_expression ren e) (rename_local_variables_var ren v)"
  by later

lemma rename_local_variables_var_same [simp]: "rename_local_variables_var ((n,m)#X) (LVariable n) = rename_local_variables_var X (LVariable m)"
  by later

lemma rename_local_variables_var_notsame [simp]: "n\<noteq>x \<Longrightarrow> m\<noteq>x \<Longrightarrow> rename_local_variables_var ((n,m)#X) (LVariable x) = LVariable x"
  by later

lemma rename_local_variables_const_expression [simp]:
  "rename_local_variables_expression X (const_expression e) = const_expression e"
  by later

lemma correctness:
  shows "LOCAL succ0. hoare {True} succ0 := call Correctness <$> ElGamal(m) {succ0}"
apply (inline "Correctness<$>ElGamal")
apply (simp) (* TODO get rid of this *)
apply (inline "keygen<$>ElGamal")
apply (simp) (* TODO get rid of this *)
apply (inline "dec<$>ElGamal")
apply (simp) (* TODO get rid of this *)
apply (inline "enc<$>ElGamal")
apply (simp) (* TODO get rid of this *)
apply (wp sample) apply skip apply auto
unfolding power_mult[symmetric] apply (subst mult.commute[where 'a=nat]) 
apply (subst mult.commute[where 'a='G]) apply (subst mult.assoc) by simp

end (* context: group *)

end (* theory *)
