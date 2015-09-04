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

(* TODO: use this *)
(*record ('pk,'sk,'m,'c) EncScheme2 = 
 keygen :: "(unit,'pk*'sk) procedure"
 enc :: "('pk*'m*unit, 'c) procedure"
 dec :: "('sk*'c*unit, 'm option) procedure"*)

(*definition "K = (%x y. x)"
definition "S = (%x y z. (x z (y z)))"

definition "X = (%x. x S K)"
definition "X' = (%x. x S K)"

lemma "op \<circ> = S (S (K S) (S (K K) (S (K S) K))) (K (S (S (K S) K) (K id)))"
apply (rule ext)+ unfolding o_def id_def K_def S_def by simp*)

(* TODO move *)
lemma lift_proc_procedure_functor_mk_untyped [simp]:
  fixes x::"'a::procedure_functor"
  shows "lift_proc (procedure_functor_mk_untyped x) i = procedure_functor_mk_untyped x"
apply (rule liftproc_wt_id[where E="[]"])
apply (rule procedure_functor_welltyped)
by simp

(* TODO move *)
lemma procedure_functor_welltyped':
  fixes p::"'a::procedure_functor"
  shows "well_typed_proc'' E (procedure_functor_mk_untyped p) (procedure_functor_type TYPE('a))"
by (rule well_typed_extend, fact procedure_functor_welltyped)

(* TODO move *)
lemma subst_proc_procedure_functor_mk_untyped [simp]:
  fixes p::"'a::procedure_functor"
  shows "subst_proc i q (procedure_functor_mk_untyped p) = procedure_functor_mk_untyped p"
by (metis Procedures.subst_lift(2) lift_proc_procedure_functor_mk_untyped)

definition procfun_K :: "'a::procedure_functor =proc=> 'b::procedure_functor =proc=> 'a::procedure_functor" where
  "procfun_K = Abs_procfun (ProcAbs (ProcAbs (ProcRef 1)))"
lemma procfun_K: "procfun_K <$> x <$> y = x"
proof -
  have wt0: "\<And>E U T. well_typed_proc'' (T#E) (ProcAbs (ProcRef 1)) (ProcTFun U T)"
    by (subst wt_ProcAbs_iff, subst wt_ProcRef_iff, simp)
  have wt1: "well_typed_proc'' [] (ProcAbs (ProcAbs (ProcRef 1)))
     (ProcTFun (procedure_functor_type TYPE('a)) (ProcTFun (procedure_functor_type TYPE('b)) (procedure_functor_type TYPE('a))))"
     apply (subst wt_ProcAbs_iff) using wt0 by auto
  have wt2: "well_typed_proc'' [] (ProcAbs (procedure_functor_mk_untyped x))
     (ProcTFun (procedure_functor_type TYPE('b)) (procedure_functor_type TYPE('a)))"
     apply (subst wt_ProcAbs_iff, rule exI, rule exI) by (auto intro!: procedure_functor_welltyped')
  show ?thesis
    unfolding procfun_K_def procfun_apply_def apply_procedure_def 
      procedure_functor_mk_untyped_procfun_def procedure_functor_mk_typed'_procfun_def
      procedure_functor_mk_typed_def
    apply (subst (2) Abs_procfun_inverse) close (simp add: wt1[simplified])
    apply (subst beta_reduce_beta) close (rule wt0) close (fact procedure_functor_welltyped')
    apply (simp, subst beta_reduce_ProcAbs) close (fact procedure_functor_welltyped')
    apply (simp, subst Abs_procfun_inverse) close (simp add: wt2)
    apply (subst beta_reduce_beta) close (fact procedure_functor_welltyped') close (fact procedure_functor_welltyped')
    by simp
qed

(* TODO: move *)
lemma beta_reduce_ProcAppl1:
  assumes "well_typed_proc'' E a (ProcTFun T U)"
  assumes "well_typed_proc'' E b T"
  shows "beta_reduce (ProcAppl a b) = beta_reduce (ProcAppl (beta_reduce a) b)"
proof -
  have "beta_reduce_proc\<^sup>*\<^sup>* a (beta_reduce a)"
    by (rule beta_reduce_def2, rule well_typed_beta_reduce, fact assms)
  hence "beta_reduce_proc\<^sup>*\<^sup>* (ProcAppl a b) (ProcAppl (beta_reduce a) b)"
    by (rule beta_reduce_proofs.rtrancl_beta_ProcAppl1)
  moreover have "beta_reduce_proc\<^sup>*\<^sup>* (ProcAppl (beta_reduce a) b) (beta_reduce (ProcAppl (beta_reduce a) b))"
    apply (rule beta_reduce_def2, rule well_typed_beta_reduce)
    apply (subst wt_ProcAppl_iff, rule exI, rule conjI)
    apply (rule beta_reduce_preserves_well_typed)
    by (fact assms)+
  ultimately have "beta_reduce_proc\<^sup>*\<^sup>* (ProcAppl a b)  (beta_reduce (ProcAppl (beta_reduce a) b))"
    by auto
  thus ?thesis
    by (rule beta_reduceI[rotated], simp)
qed

(* TODO: move *)
lemma beta_reduce_ProcAppl2:
  assumes "well_typed_proc'' E a (ProcTFun T U)"
  assumes "well_typed_proc'' E b T"
  shows "beta_reduce (ProcAppl a b) = beta_reduce (ProcAppl a (beta_reduce b))"
proof -
  have "beta_reduce_proc\<^sup>*\<^sup>* b (beta_reduce b)"
    by (rule beta_reduce_def2, rule well_typed_beta_reduce, fact assms)
  hence "beta_reduce_proc\<^sup>*\<^sup>* (ProcAppl a b) (ProcAppl a (beta_reduce b))"
    by (rule beta_reduce_proofs.rtrancl_beta_ProcAppl2)
  moreover have "beta_reduce_proc\<^sup>*\<^sup>* (ProcAppl a (beta_reduce b)) (beta_reduce (ProcAppl a (beta_reduce b)))"
    apply (rule beta_reduce_def2, rule well_typed_beta_reduce)
    apply (subst wt_ProcAppl_iff, rule exI, rule conjI)
    close (fact assms)
    apply (rule beta_reduce_preserves_well_typed)
    by (fact assms)
  ultimately have "beta_reduce_proc\<^sup>*\<^sup>* (ProcAppl a b)  (beta_reduce (ProcAppl a (beta_reduce b)))"
    by auto
  thus ?thesis
    by (rule beta_reduceI[rotated], simp)
qed

lemma beta_reduce_ProcAppl12:
  assumes "well_typed_proc'' E a (ProcTFun T U)"
  assumes "well_typed_proc'' E b T"
  shows "beta_reduce (ProcAppl a b) = beta_reduce (ProcAppl (beta_reduce a) (beta_reduce b))"
apply (subst beta_reduce_ProcAppl1) close (fact assms) close (fact assms)
apply (subst beta_reduce_ProcAppl2) apply (rule beta_reduce_preserves_well_typed) close (fact assms) close (fact assms)
by simp

definition procfun_S :: "('c::procedure_functor =proc=> 'd::procedure_functor =proc=> 'e::procedure_functor) =proc=> ('c =proc=> 'd) =proc=> 'c =proc=> 'e" where
  "procfun_S = Abs_procfun (ProcAbs (ProcAbs (ProcAbs (ProcAppl (ProcAppl (ProcRef 2) (ProcRef 0)) (ProcAppl (ProcRef 1) (ProcRef 0))))))"
lemma procfun_S: "procfun_S <$> x <$> y <$> z = (x <$> z) <$> (y <$> z)"
proof -
  let ?x = "procedure_functor_mk_untyped x"
  let ?y = "procedure_functor_mk_untyped y"
  let ?z = "procedure_functor_mk_untyped z"
  def Sx == "procfun_S <$> x"
  have Sx: "procedure_functor_mk_untyped Sx
          = beta_reduce (ProcAbs (ProcAbs (ProcAppl (ProcAppl ?x (ProcRef 0))
               (ProcAppl (ProcRef 1) (ProcRef 0)))))"
    unfolding procfun_S_def procfun_apply_def Sx_def
              procedure_functor_mk_typed_def procedure_functor_mk_typed'_procfun_def
              apply_procedure_def
    apply (subst (2) Abs_procfun_inverse[folded procedure_functor_mk_untyped_procfun_def])
     close (auto simp: wt_ProcAbs_iff wt_ProcAppl_iff wt_ProcRef_iff) 
    apply (subst (1) Abs_procfun_inverse[folded procedure_functor_mk_untyped_procfun_def])
     apply (auto simp: wt_ProcAbs_iff wt_ProcAppl_iff wt_ProcRef_iff 
                 intro!: beta_reduce_preserves_well_typed) 
     close (rule procedure_functor_welltyped[of x, simplified])
    apply (subst beta_reduce_beta)
      apply (auto simp: wt_ProcAbs_iff wt_ProcAppl_iff wt_ProcRef_iff del: exI intro!: exI) 
     by (rule procedure_functor_welltyped[of x, simplified])

   def Sxy == "Sx <$> y"
   have Sxy: "procedure_functor_mk_untyped Sxy 
            = beta_reduce (ProcAbs (ProcAppl (ProcAppl ?x (ProcRef 0)) (ProcAppl ?y (ProcRef 0))))"
    unfolding procfun_apply_def Sxy_def
              procedure_functor_mk_typed_def procedure_functor_mk_typed'_procfun_def
              apply_procedure_def
    apply (subst Abs_procfun_inverse[folded procedure_functor_mk_untyped_procfun_def])
     apply (auto simp: wt_ProcAbs_iff wt_ProcAppl_iff wt_ProcRef_iff 
                 del: exI intro!: beta_reduce_preserves_well_typed exI) 
      close (rule procedure_functor_welltyped[of Sx, simplified])
     close (rule procedure_functor_welltyped[of y, simplified])
    unfolding Sx
    apply (subst beta_reduce_ProcAppl1[symmetric])
     apply (auto simp: wt_ProcAbs_iff wt_ProcAppl_iff wt_ProcRef_iff 
                 del: exI intro!: beta_reduce_preserves_well_typed exI) 
      close (rule procedure_functor_welltyped'[of _ x, simplified])
     close (rule procedure_functor_welltyped[of y, simplified])
    apply (subst beta_reduce_beta)
     apply (auto simp: wt_ProcAbs_iff wt_ProcAppl_iff wt_ProcRef_iff 
                 del: exI intro!: beta_reduce_preserves_well_typed exI)
      close (rule procedure_functor_welltyped'[of _ x, simplified])
     by (rule procedure_functor_welltyped[of y, simplified])

   def Sxyz == "Sxy <$> z"
   have Sxyz: "procedure_functor_mk_untyped Sxyz 
            = beta_reduce (ProcAppl (ProcAppl ?x ?z) (ProcAppl ?y ?z))"
    unfolding procfun_apply_def Sxyz_def procedure_functor_mk_typed_def 
              procedure_functor_mk_typed'_procfun_def apply_procedure_def
    apply (subst procedure_functor_mk_typed_inverse')
      apply (auto simp: wt_ProcAbs_iff wt_ProcAppl_iff wt_ProcRef_iff 
                  del: exI intro!: beta_reduce_preserves_well_typed exI)
      close (rule procedure_functor_welltyped[of Sxy, simplified])
     close (rule procedure_functor_welltyped[of z, simplified])
    unfolding Sxy
    apply (subst beta_reduce_ProcAppl1[symmetric])
      apply (auto simp: wt_ProcAbs_iff wt_ProcAppl_iff wt_ProcRef_iff 
                  del: exI intro!: beta_reduce_preserves_well_typed exI)
       close (rule procedure_functor_welltyped'[of _ x, simplified])
      close (rule procedure_functor_welltyped'[of _ y, simplified])
     close (rule procedure_functor_welltyped[of z, simplified])
    apply (subst beta_reduce_beta)
      apply (auto simp: wt_ProcAbs_iff wt_ProcAppl_iff wt_ProcRef_iff 
                  del: exI intro!: beta_reduce_preserves_well_typed exI)
       close (rule procedure_functor_welltyped'[of _ x, simplified])
      close (rule procedure_functor_welltyped'[of _ y, simplified])
     by (rule procedure_functor_welltyped[of z, simplified])
    
  def xz == "x <$> z"
  have xz: "procedure_functor_mk_untyped xz = beta_reduce (ProcAppl ?x ?z)"
    unfolding procfun_apply_def xz_def procedure_functor_mk_typed_def apply_procedure_def
    apply simp
    apply (subst procedure_functor_mk_typed_inverse')
      apply (auto simp: wt_ProcAbs_iff wt_ProcAppl_iff wt_ProcRef_iff 
                  del: exI intro!: beta_reduce_preserves_well_typed exI)
     close (rule procedure_functor_welltyped[of x, simplified])
    by (rule procedure_functor_welltyped[of z, simplified])
    
  def yz == "y <$> z"
  have yz: "procedure_functor_mk_untyped yz = beta_reduce (ProcAppl ?y ?z)"
    unfolding procfun_apply_def yz_def procedure_functor_mk_typed_def apply_procedure_def
    apply simp
    apply (subst procedure_functor_mk_typed_inverse')
      apply (auto simp: wt_ProcAbs_iff wt_ProcAppl_iff wt_ProcRef_iff 
                  del: exI intro!: beta_reduce_preserves_well_typed exI)
     close (rule procedure_functor_welltyped[of y, simplified])
    by (rule procedure_functor_welltyped[of z, simplified])
  
  def xzyz == "xz <$> yz"
  have xzyz: "procedure_functor_mk_untyped xzyz 
            = beta_reduce (ProcAppl (ProcAppl ?x ?z) (ProcAppl ?y ?z))"
    unfolding procfun_apply_def procedure_functor_mk_typed_def apply_procedure_def xzyz_def
    apply simp
    apply (subst procedure_functor_mk_typed_inverse')
      apply (auto simp: wt_ProcAbs_iff wt_ProcAppl_iff wt_ProcRef_iff 
                  del: exI intro!: beta_reduce_preserves_well_typed exI)
      close (rule procedure_functor_welltyped[of xz, simplified])
     close (rule procedure_functor_welltyped[of yz, simplified])
    unfolding xz yz
    apply (subst beta_reduce_ProcAppl12[symmetric])
      apply (auto simp: wt_ProcAbs_iff wt_ProcAppl_iff wt_ProcRef_iff 
                  del: exI intro!: beta_reduce_preserves_well_typed exI)
       close (rule procedure_functor_welltyped[of x, simplified])
      close (rule procedure_functor_welltyped[of z, simplified])
     close (rule procedure_functor_welltyped[of y, simplified])
    by (rule procedure_functor_welltyped[of z, simplified])

  from Sxyz xzyz
  have "beta_reduce (procedure_functor_mk_untyped Sxyz) 
      = beta_reduce (procedure_functor_mk_untyped xzyz)" by simp
  hence "procedure_functor_mk_untyped Sxyz
       = procedure_functor_mk_untyped xzyz" by simp
  hence "Sxyz = xzyz"
    by (rule procedure_functor_mk_untyped_injective)
  thus ?thesis
    unfolding Sxyz_def Sxy_def Sx_def xzyz_def xz_def yz_def.
qed

find_theorems "well_typed_proc'' _ (procedure_functor_mk_untyped _)"

definition procfun_id :: "'a::procedure_functor =proc=> 'a" where
  "procfun_id = procfun_S <$> procfun_K <$> (procfun_K :: 'a =proc=> 'a =proc=> 'a)"
lemma procfun_id: "procfun_id <$> x = x"
  unfolding procfun_id_def procfun_S procfun_K ..

definition procfun_compose :: "('b::procedure_functor =proc=> 'c::procedure_functor)
                       =proc=> ('a::procedure_functor =proc=> 'b)
                       =proc=> ('a =proc=> 'c)" where
  "procfun_compose = procfun_S <$> (procfun_S <$> (procfun_K <$> procfun_S) <$> (procfun_S <$> 
   (procfun_K <$> procfun_K) <$> (procfun_S <$> (procfun_K <$> procfun_S) <$> procfun_K))) <$>
   (procfun_K <$> (procfun_S <$> (procfun_S <$> (procfun_K <$> procfun_S) <$> procfun_K) <$>
   (procfun_K <$> procfun_id)))"
lemma procfun_compose: "(procfun_compose <$> x <$> y) <$> z = x <$> (y <$> z)"
  unfolding procfun_compose_def procfun_S procfun_id procfun_K ..

(* TODO: make these into procfuns *)
definition "keygen = procfun_compose <$> fst_procfun <$> Rep_EncScheme'"
(*definition "keygen module = (case Rep_EncScheme module of (xkeygen,xenc,xdec) \<Rightarrow> xkeygen)"*)
definition "enc = procfun_compose <$> fst_procfun <$> (procfun_compose <$> snd_procfun <$> Rep_EncScheme')"
(*definition "enc module = (case Rep_EncScheme module of (xkeygen,xenc,xdec) \<Rightarrow> xenc)"*)
definition "dec = procfun_compose <$> snd_procfun <$> (procfun_compose <$> snd_procfun <$> Rep_EncScheme')"
(*definition "dec module = (case Rep_EncScheme module of (xkeygen,xenc,xdec) \<Rightarrow> xdec)"*)
(*definition "EncScheme x y z = Abs_EncScheme(x,y,z)"*)
lemma "keygen <$> (Abs_EncScheme (x,y,z)) = x"
  unfolding keygen_def Rep_EncScheme' procfun_compose Abs_EncScheme_inverse fst_procfun by simp
lemma "enc <$> (Abs_EncScheme (x,y,z)) = y"
  unfolding enc_def Rep_EncScheme' procfun_compose Abs_EncScheme_inverse fst_procfun snd_procfun by simp
lemma "dec <$> (Abs_EncScheme (x,y,z)) = z"
  unfolding dec_def Rep_EncScheme' procfun_compose Abs_EncScheme_inverse fst_procfun snd_procfun by simp


(* (choose,guess) *)
type_synonym ('pk,'sk,'m,'c) CPA_Adv = 
 "('pk*unit,'m*'m) procedure *
  ('c*unit,bool) procedure"

type_synonym CPA_Game = "(unit,bool)procedure"

definition_by_specification CPA_main :: "('pk,'sk,'m,'c) EncScheme * ('pk,'sk,'m,'c) CPA_Adv =proc=> CPA_Game" where
 "procfun_apply CPA_main (E,(Achoose,Aguess)) = 
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
