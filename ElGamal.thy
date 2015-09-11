theory ElGamal
imports Hoare_Tactics Procs_Typed Tactic_Inline Lang_Simplifier
begin

default_sort prog_type

class ab_group_mult = inverse + ab_semigroup_mult + monoid_mult +
  assumes left_inverse [simp]: "(inverse a) * a = 1"

lemma (in ab_group_mult) right_inverse [simp]: "a * inverse a = 1"
  by (subst mult_commute, simp)

locale group =
  (* fixes 'G *)
  fixes g::"'G::{prog_type,inverse,power,ab_group_mult}" (* generator *)
  and q::nat (* group order *)


type_synonym 'g DDH_Adv = "('g*'g*'g*unit,bool) procedure"
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

type_synonym ('pk,'sk,'m,'c) EncScheme_rep = 
 "(unit,'pk*'sk) procedure *
  ('pk*'m*unit, 'c) procedure *
  ('sk*'c*unit, 'm option) procedure"

typedef ('pk,'sk,'m,'c) EncScheme = "UNIV::('pk,'sk,'m,'c) EncScheme_rep set" ..
lemma Abs_EncScheme_inverse: "Rep_EncScheme (Abs_EncScheme x) = x"
  by (rule Abs_EncScheme_inverse, simp)

instantiation EncScheme :: (prog_type,prog_type,prog_type,prog_type)procedure_functor begin
definition "procedure_functor_type (_::('a,'b,'c,'d) EncScheme itself) == procedure_functor_type (TYPE(('a,'b,'c,'d) EncScheme_rep))"
definition "procedure_functor_mk_untyped x == procedure_functor_mk_untyped (Rep_EncScheme x)"
definition "procedure_functor_mk_typed' p == Abs_EncScheme (procedure_functor_mk_typed' p)"
instance 
  apply intro_classes
  close (unfold procedure_functor_mk_untyped_EncScheme_def procedure_functor_type_EncScheme_def, fact procedure_functor_welltyped)
  close (unfold procedure_functor_mk_untyped_EncScheme_def, fact procedure_functor_beta_reduced)
  close (unfold procedure_functor_mk_untyped_EncScheme_def procedure_functor_mk_typed'_EncScheme_def procedure_functor_type_EncScheme_def Abs_EncScheme_inverse,
         fact procedure_functor_mk_typed_inverse')
  apply (unfold procedure_functor_mk_typed'_EncScheme_def procedure_functor_mk_untyped_EncScheme_def Rep_EncScheme_inverse procedure_functor_mk_untyped_inverse')
  by (fact refl)
end

definition Rep_EncScheme' :: "('pk,'sk,'m,'c) EncScheme =proc=> ('pk,'sk,'m,'c) EncScheme_rep" where
  "Rep_EncScheme' = Abs_procfun (ProcAbs (ProcRef 0))"
lemma Rep_EncScheme': "procfun_apply Rep_EncScheme' = Rep_EncScheme"
  apply (rule ext)
  unfolding Rep_EncScheme'_def procfun_apply_def procedure_functor_mk_untyped_EncScheme_def
            procedure_functor_mk_untyped_procfun_def apply_procedure_def
  apply (subst Abs_procfun_inverse; simp?)
   apply (auto simp: wt_ProcAbs_iff wt_ProcRef_iff)
   unfolding procedure_functor_type_EncScheme_def
   close simp
  apply (subst beta_reduce_beta)
    close (auto simp: wt_ProcRef_iff)
   close (fact procedure_functor_welltyped)
  by simp

definition Abs_EncScheme' :: "('pk,'sk,'m,'c) EncScheme_rep =proc=> ('pk,'sk,'m,'c) EncScheme" where
  "Abs_EncScheme' = Abs_procfun (ProcAbs (ProcRef 0))"
lemma Abs_EncScheme': "procfun_apply Abs_EncScheme' = Abs_EncScheme"
  apply (rule ext)
  unfolding Abs_EncScheme'_def procfun_apply_def procedure_functor_mk_untyped_EncScheme_def
            procedure_functor_mk_untyped_procfun_def apply_procedure_def
  apply (subst Abs_procfun_inverse; simp?)
   apply (auto simp: wt_ProcAbs_iff wt_ProcRef_iff)
   unfolding procedure_functor_type_EncScheme_def
   close simp
  apply (subst beta_reduce_beta)
    close (auto simp: wt_ProcRef_iff)
   close (fact procedure_functor_welltyped)
  apply simp
  by (simp add: procedure_functor_mk_typed'_EncScheme_def procedure_functor_mk_typed_def)


definition "keygen = procfun_compose <$> fst_procfun <$> Rep_EncScheme'"
definition "enc = procfun_compose <$> fst_procfun <$> (procfun_compose <$> snd_procfun <$> Rep_EncScheme')"
definition "dec = procfun_compose <$> snd_procfun <$> (procfun_compose <$> snd_procfun <$> Rep_EncScheme')"

lemma keygen[simp]: "keygen <$> (Abs_EncScheme (x,y,z)) = x"
  unfolding keygen_def Rep_EncScheme' procfun_compose Abs_EncScheme_inverse fst_procfun by simp
lemma enc[simp]: "enc <$> (Abs_EncScheme (x,y,z)) = y"
  unfolding enc_def Rep_EncScheme' procfun_compose Abs_EncScheme_inverse fst_procfun snd_procfun by simp
lemma dec[simp]: "dec <$> (Abs_EncScheme (x,y,z)) = z"
  unfolding dec_def Rep_EncScheme' procfun_compose Abs_EncScheme_inverse fst_procfun snd_procfun by simp


(* (choose,guess) *)
type_synonym ('pk,'sk,'m,'c) CPA_Adv = 
 "('pk*unit,'m*'m) procedure *
  ('c*unit,bool) procedure"

type_synonym CPA_Game = "(unit,bool)procedure"

procedure CPA_main :: "('pk,'sk,'m,'c) EncScheme * ('pk,'sk,'m,'c) CPA_Adv =proc=> CPA_Game" where
 "CPA_main <$> (E,(Achoose,Aguess)) = 
  LOCAL pk sk m0 m1 b c b' tmp1 tmp2.
  proc () {
    tmp1 := call keygen<$>E();
    pk := fst tmp1;
    sk := snd tmp1;
    tmp2 := call Achoose(pk);
    m0 := fst tmp2;
    m1 := snd tmp2;
    b <- uniform UNIV;
    c := call enc<$>E(pk, if b then m1 else m0);
    b' := call Aguess(c);
    return b'=b
  }"

definition (in group) ElGamal :: "('G,nat,'G,'G\<times>'G) EncScheme" where
 "ElGamal = LOCAL pk m0 c sk sk' y gm gy.
   Abs_EncScheme (proc() { sk <- uniform {0..<q}; return (g^sk, sk) },
                  proc(pk,m0) { y <- uniform {0..<q}; return (g^y, pk^y * m0) },
                  proc(sk',c) { gy := fst c; gm := snd c; return Some (gm * inverse (gy^sk')) })"


procedure Correctness :: "(_,_,_,_) EncScheme =proc=> (_*unit,bool)procedure" where
  "Correctness <$> E = LOCAL m1 m2 succ pksk c1.
  proc(m1) {
    pksk := call keygen<$>E();
    c1 := call enc<$>E(fst pksk, m1);
    m2 := call dec<$>E(snd pksk, c1);
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


end

lemma (in group) correctness:
  shows "LOCAL succ0. hoare {True} succ0 := call Correctness <$> ElGamal(m) {succ0}"
apply (inline "Correctness<$>ElGamal")
apply (inline "keygen<$>ElGamal")
apply (inline "dec<$>ElGamal")
apply (inline "enc<$>ElGamal")
apply (wp sample) apply skip apply auto
unfolding power_mult[symmetric] apply (subst mult.commute[where 'a=nat]) 
apply (subst mult.commute[where 'a='G]) apply (subst mult.assoc) by simp

end
