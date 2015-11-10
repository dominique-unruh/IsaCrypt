theory ElGamal
imports Hoare_Tactics Procs_Typed Tactic_Inline Lang_Simplifier RHL_Typed
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

type_synonym Game = "(unit,bool) procedure"
type_synonym 'g DDH_Adv = "('g*'g*'g,bool) procedure"

procedure (in group) DDH0 :: "'G DDH_Adv =proc=> Game" where
  "DDH0 <$> A = 
    LOCAL x y b.
    proc () {
      x <- uniform {0..<q};
      y <- uniform {0..<q};
      b := call A (g^x, g^y, g^(x*y));
      return True
    }"

procedure (in group) DDH1 :: "'G DDH_Adv =proc=> Game" where
  "DDH1 <$> A = 
    LOCAL x y z b.
    proc () {
      x <- uniform {0..<q};
      y <- uniform {0..<q};
      z <- uniform {0..<q};
      b := call A (g^x, g^y, g^z);
      return True
    }"

subsection {* PKE definitions *}


module_type ('pk,'sk,'m,'c) EncScheme =
  keygen :: "(unit,'pk*'sk) procedure"
  enc :: "('pk*'m, 'c) procedure"
  dec :: "('sk*'c, 'm option) procedure"

(*module_type ('pk,'sk,'m,'c) Adversary =
  choos :: "('pk,'m*'m)procedure" 
  "guess" :: "('c,bool)procedure"

procedure CPA :: "('pk,'sk,'m,'c) EncScheme * ('pk,'sk,'m,'c) Adversary =proc=> Game" where
  "CPA<$>(E,A) = LOCAL pk sk m0 m1 c b b'. proc() {
    (pk, sk) := call keygen<$>E();
    (m0, m1) := call choos<$>A(pk);
    b        <- uniform UNIV;
    c        := call enc<$>E(pk, if b then m1 else m0);
    b'       := call guess<$>A(c);
    return (b' = b)
  }"*)

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

(* These should be generated by module_type EncScheme *)

lemma aux1 [reduce_procfun.safe]:
  assumes "schematic=Abs_EncScheme(A,B,C)"
  assumes "A=Y"
  shows "keygen<$>schematic = Y"
using assms by simp

lemma aux2 [reduce_procfun.safe]:
  assumes "schematic=Abs_EncScheme(A,B,C)"
  assumes "B=Y"
  shows "enc<$>schematic = Y"
using assms by simp

lemma aux3 [reduce_procfun.safe]:
  assumes "schematic=Abs_EncScheme(A,B,C)"
  assumes "C=Y"
  shows "dec<$>schematic = Y"
using assms by simp

procedure (in group) ElGamal :: "('G, nat, 'G, 'G\<times>'G) EncScheme" where
    "keygen<$>ElGamal = LOCAL sk. proc() { sk <- uniform {0..<q}; return (g^sk, sk) }"
and "enc<$>ElGamal = LOCAL pk m y. proc(pk,m) { y <- uniform {0..<q}; return (g^y, pk^y * m) }"
and "dec<$>ElGamal = LOCAL sk c1 c2 gy gm. proc(sk,(c1,c2)) { gy := c1; gm := c2; return Some (gm * inverse (gy^sk)) }"

thm group.keygen_ElGamal_def
print_theorems

procedure Correctness :: "(_,_,_,_) EncScheme =proc=> (_,bool)procedure" where
  "Correctness <$> E = LOCAL m m2 pk sk c.
  proc(m) {
    (pk,sk) := call keygen<$>E ();
    c := call enc<$>E (pk, m);
    m2 := call dec<$>E (sk, c);
    return (m2 = Some m)
  }"

context group begin

lemma correctness:
  shows "LOCAL succ0. hoare {True} succ0 := call Correctness <$> ElGamal(m) {succ0}"
apply (inline "Correctness<$>ElGamal")
apply (inline "keygen<$>ElGamal")
apply (inline "dec<$>ElGamal")
apply (inline "enc<$>ElGamal")
apply (wp sample) apply skip apply auto
unfolding power_mult[symmetric] apply (subst mult.commute[where 'a=nat])
apply (subst mult.commute[where 'a='G]) apply (subst mult.assoc) by simp

type_synonym 'g ElGamal_Adv = "('g, nat, 'g, 'g\<times>'g) CPA_Adv"

procedure DDHAdv :: "'G ElGamal_Adv =proc=> 'G DDH_Adv" where
  "DDHAdv <$> A = LOCAL gx gy gz m0 m1 b b'. 
    proc (gx, gy, gz) {
      (m0, m1) := call pick<$>A(gx);
      b  <- uniform UNIV;
      b' := call guess<$>A(gy, gz * (if b then m1 else m0));
      return b' = b
  }"



(* TODO move, add syntax *)
definition "game_probability game args mem E == 
  LOCAL res. 
  probability 
    (denotation (callproc (variable_pattern res) game (const_expression args)) mem)
    (\<lambda>m. E (memory_lookup m res))"

(* TODO move *)
lemma byequiv_rule:
  assumes "hoare {&1=&2} (res := call p1(a1)) ~ (res := call p2(a2)) {E res\<^sub>1 = F res\<^sub>2}"
  shows "game_probability p1 a1 m E = game_probability p2 a2 m F" 
SORRY

lemma cpa_ddh0:
  "game_probability (CPA_main<$>(ElGamal,A)) () m (\<lambda>res. res)
 = game_probability (DDH0<$>(DDHAdv<$>A)) () m (\<lambda>res. res)" 
apply (rule byequiv_rule)
apply (inline "CPA_main<$>(ElGamal,A)")
apply (inline "DDH0<$>(DDHAdv<$>A)")

(* 
  local lemma cpa_ddh0 &m: 
      Pr[CPA(ElGamal,A).main() @ &m : res] =
      Pr[DDH0(DDHAdv(A)).main() @ &m : res].
  proof.
    byequiv => //;proc;inline *.
    swap{1} 7 -5.
    auto;call (_:true);auto;call (_:true);auto;progress;smt.
  qed.

  local module Gb = {
    proc main () : bool = {
      var x, y, z, m0, m1, b, b';
      x  = $FDistr.dt;
      y  = $FDistr.dt;
      (m0,m1) = A.choose(g^x);
      z  = $FDistr.dt;
      b' = A.guess(g^y, g^z);
      b  = ${0,1};
      return b' = b;
    }
  }.

  local lemma ddh1_gb &m: 
      Pr[DDH1(DDHAdv(A)).main() @ &m : res] = 
      Pr[Gb.main() @ &m : res].
  proof.
    byequiv => //;proc;inline *.
    swap{1} 3 2;swap{1} [5..6] 2;swap{2} 6 -2.
    auto;call (_:true);wp.
    rnd (fun z, z + log(if b then m1 else m0){2}) 
        (fun z, z - log(if b then m1 else m0){2}).
    auto;call (_:true);auto;progress; (algebra || smt).
  qed.

  axiom Ac_l : islossless A.choose.
  axiom Ag_l : islossless A.guess.

  local lemma Gb_half &m: 
     Pr[Gb.main()@ &m : res] = 1%r/2%r.
  proof.
    byphoare => //;proc.
    rnd  ((=) b')=> //=.
    call Ag_l;auto;call Ac_l;auto;progress;smt. 
  qed.

  lemma conclusion &m :
    `| Pr[CPA(ElGamal,A).main() @ &m : res] - 1%r/2%r | =
    `| Pr[DDH0(DDHAdv(A)).main() @ &m : res] -  
         Pr[DDH1(DDHAdv(A)).main() @ &m : res] |. 
  proof.
   by rewrite (cpa_ddh0 &m) (ddh1_gb &m) (Gb_half &m).
  qed.
*)

end (* context: group *)


end (* theory *)
