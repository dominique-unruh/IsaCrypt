theory Procs_Typed
imports TermX_Antiquot Lang_Typed Procedures
keywords "procedure" :: thy_decl
     and "procedure'" :: thy_goal
begin

subsection {* Procedure functors *}

class procedure_functor =
  fixes procedure_functor_type :: "'a itself \<Rightarrow> procedure_type_open"
  fixes procedure_functor_mk_untyped :: "'a \<Rightarrow> procedure_rep"
  fixes procedure_functor_mk_typed' :: "procedure_rep \<Rightarrow> 'a"
  assumes procedure_functor_welltyped: "well_typed_proc'' [] (procedure_functor_mk_untyped (p::'a)) (procedure_functor_type TYPE('a))"
  assumes procedure_functor_beta_reduced [simp]: "beta_reduced (procedure_functor_mk_untyped (p::'a))"
  assumes procedure_functor_mk_typed_inverse': 
    "well_typed_proc'' [] q (procedure_functor_type TYPE('a)) \<Longrightarrow> beta_reduced q
       \<Longrightarrow> procedure_functor_mk_untyped (procedure_functor_mk_typed' q) = q"
  assumes procedure_functor_mk_untyped_inverse' [simp]:
    "procedure_functor_mk_typed' (procedure_functor_mk_untyped p) = p"

definition "procedure_functor_mk_typed p = procedure_functor_mk_typed' (beta_reduce p)"

lemma procedure_functor_welltyped':
  fixes p::"'a::procedure_functor"
  shows "well_typed_proc'' E (procedure_functor_mk_untyped p) (procedure_functor_type TYPE('a))"
by (rule well_typed_extend, fact procedure_functor_welltyped)

lemma procedure_functor_mk_typed_inverse: 
    "well_typed_proc'' [] q (procedure_functor_type TYPE('a::procedure_functor))
       \<Longrightarrow> procedure_functor_mk_untyped (procedure_functor_mk_typed q :: 'a) = beta_reduce q"
  unfolding procedure_functor_mk_typed_def 
  apply (subst procedure_functor_mk_typed_inverse')
  by (rule beta_reduce_preserves_well_typed, auto)

lemma procedure_functor_mk_untyped_inverse [simp]:
    "procedure_functor_mk_typed (procedure_functor_mk_untyped p) = p"
  unfolding procedure_functor_mk_typed_def
  apply (subst beta_reduced_beta_reduce_id)
  close (fact procedure_functor_beta_reduced)
  by (fact procedure_functor_mk_untyped_inverse')


lemma procedure_functor_mk_untyped_injective:
    "procedure_functor_mk_untyped p = procedure_functor_mk_untyped q \<Longrightarrow> p = q"
using procedure_functor_mk_untyped_inverse by metis

lemma lift_proc_procedure_functor_mk_untyped [simp]:
  fixes x::"'a::procedure_functor"
  shows "lift_proc (procedure_functor_mk_untyped x) i = procedure_functor_mk_untyped x"
apply (rule liftproc_wt_id[where E="[]"])
apply (rule procedure_functor_welltyped)
by simp

lemma subst_proc_procedure_functor_mk_untyped [simp]:
  fixes p::"'a::procedure_functor"
  shows "subst_proc i q (procedure_functor_mk_untyped p) = procedure_functor_mk_untyped p"
by (metis Procedures.subst_lift(2) lift_proc_procedure_functor_mk_untyped)

subsubsection "Procedure functions"

typedef ('a::procedure_functor,'b::procedure_functor) procfun = "{p::procedure_rep.
  well_typed_proc'' [] p (ProcTFun (procedure_functor_type TYPE('a)) (procedure_functor_type TYPE('b)))
  \<and> beta_reduced p}"
  apply (rule exI[of _ "ProcAbs (procedure_functor_mk_untyped (undefined::'b))"], auto)
  by (rule wt_ProcAbs, rule well_typed_extend, rule procedure_functor_welltyped)

type_notation "procfun" (infixr "=proc=>" 0)

instantiation procfun :: (procedure_functor,procedure_functor) procedure_functor begin
definition [simp]: "procedure_functor_type (_::('a,'b)procfun itself)
     == ProcTFun (procedure_functor_type TYPE('a)) (procedure_functor_type TYPE('b))"
definition "procedure_functor_mk_untyped == Rep_procfun"
definition "procedure_functor_mk_typed' == Abs_procfun"
instance apply intro_classes 
  unfolding procedure_functor_type_procfun_def procedure_functor_mk_untyped_procfun_def
            procedure_functor_mk_typed'_procfun_def
  using Rep_procfun close auto
  close (metis Rep_procfun mem_Collect_eq)
  using Rep_procfun_inverse apply auto
  using Abs_procfun_inverse by blast
end

definition procfun_apply :: "('a::procedure_functor,'b::procedure_functor)procfun \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "<$>" 100)where
   "procfun_apply f p = procedure_functor_mk_typed (apply_procedure (procedure_functor_mk_untyped f) (procedure_functor_mk_untyped p))"
lemma procedure_functor_mk_untyped_procfun_apply:
  "procedure_functor_mk_untyped (a <$> b) = beta_reduce (ProcAppl (procedure_functor_mk_untyped a) (procedure_functor_mk_untyped b))"
unfolding procfun_apply_def apply_procedure_def
apply (subst procedure_functor_mk_typed_inverse)
 apply (rule beta_reduce_preserves_well_typed)
 apply (subst wt_ProcAppl_iff, rule exI, rule conjI)
  close (fact procedure_functor_welltyped[of a, simplified])
 close (fact procedure_functor_welltyped[of b, simplified])
by simp

instantiation prod :: (procedure_functor,procedure_functor) procedure_functor begin
definition [simp]: "procedure_functor_type (_::('a*'b) itself)
     == ProcTPair (procedure_functor_type TYPE('a)) (procedure_functor_type TYPE('b))"
definition "procedure_functor_mk_untyped == 
  (\<lambda>(x,y). ProcPair (procedure_functor_mk_untyped x) (procedure_functor_mk_untyped y))"
definition "procedure_functor_mk_typed' p == 
  (case p of ProcPair x y \<Rightarrow> (procedure_functor_mk_typed' x, procedure_functor_mk_typed' y))"
instance proof intro_classes 
  show "\<And>p::'a\<times>'b. well_typed_proc'' [] (procedure_functor_mk_untyped p) (procedure_functor_type TYPE('a \<times> 'b))"
  unfolding  procedure_functor_mk_untyped_prod_def 
    by (auto, rule well_typed''_well_typed_proc''.intros, simp_all add: procedure_functor_welltyped)
  fix p::"'a\<times>'b"
  show "beta_reduced (procedure_functor_mk_untyped p)"
    unfolding procedure_functor_mk_untyped_prod_def
    by (case_tac p, simp)
next
  fix q assume wt_q: "well_typed_proc'' [] q (procedure_functor_type TYPE('a\<times>'b))" and br_q: "beta_reduced q"
  then obtain q1 q2 where q: "q = ProcPair q1 q2"
    by (rule_tac well_typed_ProcTPair_ProcPair, auto)
  from br_q have br_q1: "beta_reduced q1" and br_q2: "beta_reduced q2" 
    unfolding q by auto
  from wt_q have wt_q1: "well_typed_proc'' [] q1 (procedure_functor_type TYPE('a))"
             and wt_q2: "well_typed_proc'' [] q2 (procedure_functor_type TYPE('b))"
    unfolding q unfolding wt_ProcPair_iff procedure_functor_type_prod_def by auto
  show "procedure_functor_mk_untyped (procedure_functor_mk_typed' q :: 'a\<times>'b) = q"
    unfolding procedure_functor_mk_typed'_prod_def procedure_functor_mk_untyped_prod_def q
    apply auto 
    close (rule procedure_functor_mk_typed_inverse', fact wt_q1, fact br_q1)
    by (rule procedure_functor_mk_typed_inverse', fact wt_q2, fact br_q2)
next
  fix p::"'a\<times>'b"
  show "procedure_functor_mk_typed' (procedure_functor_mk_untyped p) = p"
    unfolding procedure_functor_mk_typed'_prod_def procedure_functor_mk_untyped_prod_def
    using procedure_functor_mk_untyped_inverse' by (cases p, auto)
qed
end


(* TODO move *)
lemma beta_reduce_procedure_functor_mk_untyped [simp]:
  "beta_reduce (procedure_functor_mk_untyped x) = procedure_functor_mk_untyped x"
by (simp add: beta_reduced_beta_reduce_id)


definition fst_procfun :: "('a::procedure_functor*'b::procedure_functor) =proc=> 'a" where
  "fst_procfun = Abs_procfun (ProcAbs (ProcUnpair True (ProcRef 0)))"
lemma fst_procfun [simp]: "procfun_apply fst_procfun x = fst x"
  unfolding fst_procfun_def procfun_apply_def procedure_functor_mk_untyped_procfun_def 
            apply_procedure_def
  apply (subst Abs_procfun_inverse)
  close (auto simp: wt_ProcAbs_iff wt_ProcUnpair_iff wt_ProcRef_iff)
  apply (cases x, auto)
  unfolding procedure_functor_mk_untyped_prod_def
  apply auto
  apply (subst beta_reduce_beta)
    close (auto simp: wt_ProcAbs_iff wt_ProcUnpair_iff wt_ProcRef_iff)
    close (auto simp: wt_ProcAbs_iff wt_ProcUnpair_iff wt_ProcRef_iff wt_ProcPair_iff; rule procedure_functor_welltyped)+
  apply simp  apply (subst beta_reduce_ProcUnpair1)
    close (rule procedure_functor_welltyped)
  by (simp add: beta_reduced_beta_reduce_id)


definition snd_procfun :: "('a::procedure_functor*'b::procedure_functor) =proc=> 'b" where
  "snd_procfun = Abs_procfun (ProcAbs (ProcUnpair False (ProcRef 0)))"
lemma snd_procfun [simp]: "procfun_apply snd_procfun x = snd x"
  unfolding snd_procfun_def procfun_apply_def procedure_functor_mk_untyped_procfun_def 
            apply_procedure_def
  apply (subst Abs_procfun_inverse)
    close (auto simp: wt_ProcAbs_iff wt_ProcUnpair_iff wt_ProcRef_iff)
  apply (cases x, auto)
  unfolding procedure_functor_mk_untyped_prod_def
  apply auto
  apply (subst beta_reduce_beta)
    close (auto simp: wt_ProcAbs_iff wt_ProcUnpair_iff wt_ProcRef_iff)
    close (auto simp: wt_ProcAbs_iff wt_ProcUnpair_iff wt_ProcRef_iff wt_ProcPair_iff; rule procedure_functor_welltyped)+
  apply simp  apply (subst beta_reduce_ProcUnpair2)
    close (rule procedure_functor_welltyped)
  by (simp add: beta_reduced_beta_reduce_id)



definition pair_procfun :: "('a::procedure_functor) =proc=> ('b::procedure_functor) =proc=> ('a*'b)" where
  "pair_procfun = Abs_procfun (ProcAbs (ProcAbs (ProcPair (ProcRef 1) (ProcRef 0))))"
lemma pair_procfun [simp]: "procfun_apply (procfun_apply pair_procfun a) b = (a,b)"
  unfolding pair_procfun_def procfun_apply_def procedure_functor_mk_untyped_procfun_def apply_procedure_def
  unfolding procedure_functor_mk_typed_def beta_reduce_idem 
  apply (subst Abs_procfun_inverse)
   close (auto simp: wt_ProcAbs_iff wt_ProcUnpair_iff wt_ProcRef_iff wt_ProcPair_iff)
  apply (subst beta_reduce_beta)
    close (auto simp: wt_ProcAbs_iff wt_ProcUnpair_iff wt_ProcRef_iff wt_ProcPair_iff)
   close (rule procedure_functor_welltyped)
  apply (simp?, subst beta_reduce_ProcAbs[where E="[_]"])
   apply (subst wt_ProcPair_iff, auto del: exI intro!: exI)[1]
    close (rule procedure_functor_welltyped')
    close (subst wt_ProcRef_iff, simp)
  apply (subst beta_reduce_ProcPair) 
    close (fact procedure_functor_welltyped)
   apply (subst wt_ProcRef_iff; simp)
   close auto
  apply (subst beta_reduce_procedure_functor_mk_untyped)
  apply (subst beta_reduce_ProcRef)
  unfolding procedure_functor_mk_typed'_procfun_def
  apply (subst Abs_procfun_inverse; auto?)
   close (auto simp: wt_ProcAbs_iff wt_ProcUnpair_iff wt_ProcRef_iff wt_ProcPair_iff procedure_functor_welltyped well_typed_extend)
  apply (subst beta_reduce_beta)
    apply (subst wt_ProcPair_iff)
    apply (rule exI, rule exI; auto)
     apply (rule well_typed_extend)
     close (fact procedure_functor_welltyped)
    close (subst wt_ProcRef_iff; auto)
   close (rule well_typed_extend, rule procedure_functor_welltyped)
  apply simp
  apply (subst beta_reduce_ProcPair)
    close (fact procedure_functor_welltyped)
   close (fact procedure_functor_welltyped)
  apply (subst beta_reduce_procedure_functor_mk_untyped)
  apply (subst beta_reduce_procedure_functor_mk_untyped)
  by (simp add: procedure_functor_mk_typed'_prod_def)

subsubsection "Procedures"

instantiation procedure_ext :: (procargs,prog_type,singleton) procedure_functor begin
definition [simp]: "procedure_functor_type (_::('a,'b,'c)procedure_ext itself) == ProcTSimple (procedure_type TYPE(('a,'b,'c)procedure_ext))"
definition "procedure_functor_mk_untyped == mk_procedure_untyped"
definition "procedure_functor_mk_typed' == mk_procedure_typed"
instance proof intro_classes
  show "\<And>p::('a, 'b, 'c) procedure_scheme. well_typed_proc'' [] (procedure_functor_mk_untyped p)
          (procedure_functor_type TYPE(('a, 'b, 'c) procedure_scheme))"
    unfolding procedure_functor_type_procedure_ext_def procedure_functor_mk_untyped_procedure_ext_def 
    using well_typed_proc_well_typed_proc'' mk_procedure_untyped by metis
  show "\<And>p::('a, 'b, 'c) procedure_scheme. beta_reduced (procedure_functor_mk_untyped p)" 
    unfolding procedure_functor_mk_untyped_procedure_ext_def 
    using well_typed_proc_beta_reduced mk_procedure_untyped by auto
  show "\<And>q. well_typed_proc'' [] q (procedure_functor_type TYPE(('a, 'b, 'c) procedure_scheme)) \<Longrightarrow>
         beta_reduced q \<Longrightarrow> procedure_functor_mk_untyped (procedure_functor_mk_typed' q::('a, 'b, 'c) procedure_scheme) = q"
  proof -
    fix q assume wtq: "well_typed_proc'' [] q (procedure_functor_type TYPE(('a, 'b, 'c) procedure_scheme))"
    assume betaq: "beta_reduced q"
    obtain body args ret where q:"q = Proc body args ret"
      apply (rule_tac p=q in well_typed_ProcTSimple_Proc) 
        close (rule wtq[unfolded procedure_functor_type_procedure_ext_def])
        close (rule betaq)
        by metis
    have wtq0: "well_typed_proc q" 
      apply (rule well_typed''_well_typed)
        close (rule wtq[unfolded procedure_functor_type_procedure_ext_def])
        by (rule betaq)  
    hence "well_typed body" unfolding q by simp
    moreover have "\<And>v. v \<in> set args \<Longrightarrow> \<not> vu_global v"
      by (metis wtq0 q well_typed_proc.simps(1))
    moreover have "distinct args"
      by (metis wtq0 q well_typed_proc.simps(1))
    moreover
    have pt_q: "proctype_of q = procedure_type TYPE(('a, 'b, 'c) procedure_scheme)"
      apply (rule well_typed_proc''_proctype_of)
        close (rule wtq[unfolded procedure_functor_type_procedure_ext_def])
        by (rule betaq)  
    have "args \<in> procargvars TYPE('a)" 
      apply (rule procedure_type_procargvars)
        close (fact pt_q[unfolded q])
        by (fact wtq0[unfolded q])
    moreover have "eu_type ret = Type TYPE('b)" 
      using pt_q by (simp add: q procedure_type_def)
    ultimately show "procedure_functor_mk_untyped (procedure_functor_mk_typed' q::('a, 'b, 'c) procedure_scheme) = q"
      unfolding procedure_functor_mk_untyped_procedure_ext_def procedure_functor_mk_typed'_procedure_ext_def q
      by (subst mk_procedure_typed_inverse, auto)
  qed
  show "\<And>p::('a, 'b, 'c) procedure_scheme. 
        procedure_functor_mk_typed' (procedure_functor_mk_untyped p) = p"
    unfolding procedure_functor_mk_untyped_procedure_ext_def procedure_functor_mk_typed'_procedure_ext_def
    by (rule mk_procedure_untyped_inverse)
qed

end

subsubsection {* Combinators *}


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



subsection {* Support for defining typed procedure functors *}

definition "subst_prog1 (p::'a::procedure_functor) q pr ==
  well_typed'' [procedure_functor_type TYPE('a)] q 
\<and> Abs_program (beta_reduce' (subst_proc_in_prog 0 (procedure_functor_mk_untyped p) (beta_reduce' q))) = pr"
(*definition "subst_proc1 (p::'a::procedure_functor) q (pr::('b::procargs,'c::prog_type)procedure) == 
  well_typed_proc'' [procedure_functor_type TYPE('a)] q (ProcTSimple (procedure_type TYPE(('b,'c)procedure)))
  \<and> procedure_functor_mk_typed (subst_proc 0 (procedure_functor_mk_untyped p) (beta_reduce q)) = pr"*)

locale reduce_procfun begin

lemma proc: shows "p = (p::('a,'b)procedure)" ..


lemma apply1:
  fixes p body body0 retval args and arg_proc::"'a::procedure_functor"
  assumes subst: "subst_prog1 arg_proc body PROGRAM[\<guillemotleft>body0\<guillemotright>]"
  defines "p0==procedure_functor_mk_typed (ProcAbs (Proc body (Rep_procargvars args) (mk_expression_untyped retval)))"
  shows "procfun_apply p0 arg_proc = \<lparr> p_body=body0, p_args=args, p_return=retval \<rparr>"
proof -
  have wt1: "well_typed_proc'' [procedure_functor_type TYPE('a)]
     (Proc body (mk_procargvars_untyped args) (mk_expression_untyped retval))
     (ProcTSimple (procedure_type TYPE(('b, 'c) procedure)))"
    apply (subst wt_Proc_iff, auto simp: procedure_type_def)
    using assms unfolding subst_prog1_def close auto
    using Rep_procargvars procargvars_local close auto
    using Rep_procargvars procargvars_distinct by auto

  have wt2: "well_typed_proc'' [] (ProcAbs (Proc body (mk_procargvars_untyped args) (mk_expression_untyped retval)))
        (procedure_functor_type TYPE('a =proc=> ('b, 'c) procedure))" 
    apply simp apply (rule wt_ProcAbs) by (fact wt1)

  have wt_body: "well_typed'' [procedure_functor_type TYPE('a)] body"
    using subst unfolding subst_prog1_def by simp

  have wt_subst: "well_typed'' [] (subst_proc_in_prog 0 (procedure_functor_mk_untyped arg_proc) (beta_reduce' body))"
    apply (rule well_typed_subst_proc[where F="[]", simplified])
    close (rule procedure_functor_welltyped)
    apply (rule beta_reduce_preserves_well_typed)
    by (rule wt_body)

  have aux: "Rep_program (Abs_program (beta_reduce' (subst_proc_in_prog 0 
             (procedure_functor_mk_untyped arg_proc) (beta_reduce' body)))) = Rep_program body0"
    using subst unfolding subst_prog1_def program_def by auto
  have subst': "beta_reduce' (subst_proc_in_prog 0 (procedure_functor_mk_untyped arg_proc)
                    (beta_reduce' body)) = mk_program_untyped body0"
    apply (subst Abs_program_inverse[symmetric], auto)
    apply (rule well_typed''_well_typed)
    close (metis beta_reduce_preserves_well_typed(1) wt_subst)
    apply (rule beta_reduce'_def2)
    close (metis beta_reduce_proofs.well_typed_beta_reduce(1) wt_subst)
    by (rule aux)

  show ?thesis
    unfolding p0_def procfun_apply_def apply_procedure_def
    apply (subst procedure_functor_mk_typed_inverse)
      close (fact wt2)
    apply (subst beta_reduce_ProcAbs)
      close (fact wt1)
    apply (subst beta_reduce_beta) 
      close (rule beta_reduce_preserves_well_typed, fact wt1)
      close (rule procedure_functor_welltyped)
    apply (rule procedure_functor_mk_untyped_injective)
    apply (subst procedure_functor_mk_typed_inverse)
      apply (rule beta_reduce_preserves_well_typed)
      apply (rule well_typed_subst_proc(2)[where F="[]", simplified])
        close (fact procedure_functor_welltyped)  
      apply (rule beta_reduce_preserves_well_typed(2)[where T="procedure_functor_type TYPE(('b,'c)procedure)"])
      apply (simp add: procedure_type_def)
      close (metis procedure_type_def wt1)
    apply (subst beta_reduce_Proc)
      close (fact wt_body)
    unfolding procedure_functor_mk_untyped_procedure_ext_def mk_procedure_untyped_def
    apply simp
    apply (subst beta_reduce_Proc)
      close (fact wt_subst)
    apply simp      
    by (fact subst')
qed

lemma seq:
  assumes "subst_prog1 p q1 PROGRAM[\<guillemotleft>c1\<guillemotright>]"
  assumes "subst_prog1 p q2 PROGRAM[\<guillemotleft>c2\<guillemotright>]"
  defines "q == Seq q1 q2"
  shows "subst_prog1 p q PROGRAM[\<guillemotleft>c1\<guillemotright>; \<guillemotleft>c2\<guillemotright>]"
proof - 
  have wt_q1: "well_typed'' [procedure_functor_type TYPE('a)] q1" 
   and wt_q2: "well_typed'' [procedure_functor_type TYPE('a)] q2"
    using assms unfolding subst_prog1_def by auto 
  hence wt_seq: "well_typed'' [procedure_functor_type TYPE('a)] (Seq q1 q2)"
    by (rule_tac wt_Seq, simp)
  have wt_subst_q1:  "well_typed'' [] (subst_proc_in_prog 0 (procedure_functor_mk_untyped p) (beta_reduce' q1))"
      apply (rule well_typed_subst_proc[where F="[]", simplified])
      close (rule procedure_functor_welltyped)
      apply (rule beta_reduce_preserves_well_typed)
      by (fact wt_q1)
  have wt_subst_q2:  "well_typed'' [] (subst_proc_in_prog 0 (procedure_functor_mk_untyped p) (beta_reduce' q2))"
      apply (rule well_typed_subst_proc[where F="[]", simplified])
      close (rule procedure_functor_welltyped)
      apply (rule beta_reduce_preserves_well_typed)
      by (fact wt_q2)
  have q1_c1: "beta_reduce' (subst_proc_in_prog 0 (procedure_functor_mk_untyped p) (beta_reduce' q1)) =
    mk_program_untyped c1"
    apply (subst Abs_program_inject[symmetric], auto)
      apply (rule well_typed''_well_typed)
      apply (rule beta_reduce_preserves_well_typed)
        close (fact wt_subst_q1)
      apply (rule beta_reduced_beta_reduce')
      apply (subst Rep_program_inverse)
      using assms(1) unfolding subst_prog1_def program_def by auto
  have q2_c2: "beta_reduce' (subst_proc_in_prog 0 (procedure_functor_mk_untyped p) (beta_reduce' q2)) =
    mk_program_untyped c2"
    apply (subst Abs_program_inject[symmetric], auto)
      apply (rule well_typed''_well_typed)
      apply (rule beta_reduce_preserves_well_typed)
        close (fact wt_subst_q2)
      apply (rule beta_reduced_beta_reduce')
      apply (subst Rep_program_inverse)
      using assms(2) unfolding subst_prog1_def program_def by auto
  have eq: "Abs_program
     (beta_reduce' (subst_proc_in_prog 0 (procedure_functor_mk_untyped p) (beta_reduce' (Seq q1 q2)))) =
    Abs_program (Seq (mk_program_untyped c1) (mk_program_untyped c2))"
    apply (tactic "cong_tac @{context} 1", fact refl)
    apply (subst beta_reduce_Seq)
      close (fact wt_q1) close (fact wt_q2)
    apply simp
    apply (subst beta_reduce_Seq)
      close (fact wt_subst_q1) close (fact wt_subst_q2)
    by (auto simp: q1_c1 q2_c2)
  from wt_seq eq show ?thesis
    unfolding subst_prog1_def q_def program_def seq_def by auto
qed

(* TODO: move *)
lemma subst_well_typed_id:
  shows "well_typed p' \<Longrightarrow> subst_proc_in_prog n q p' = p'"
    and "well_typed_proc p \<Longrightarrow> subst_proc n q p = p"
apply (induction p' and p)
apply auto apply (rename_tac x p a)
by (case_tac p, auto)


lemma closed:
  fixes q c p
  defines "q == mk_program_untyped c"
  shows "subst_prog1 p q PROGRAM[\<guillemotleft>c\<guillemotright>]"
unfolding q_def subst_prog1_def program_def apply auto
apply (metis Rep_program mem_Collect_eq well_typed_extend(1) well_typed_well_typed'')
apply (subst beta_reduced_beta_reduce_id')
apply (subst subst_well_typed_id)
close (metis beta_reduce_preserves_well_typed(1) beta_reduced_beta_reduce' well_typed''_well_typed(1) well_typed_mk_program_untyped well_typed_well_typed'')
close (rule beta_reduced_beta_reduce')
apply (subst subst_well_typed_id)
apply (metis beta_reduce_preserves_well_typed(1) beta_reduced_beta_reduce' well_typed''_well_typed(1) well_typed_mk_program_untyped well_typed_well_typed'')
apply (subst beta_reduced_beta_reduce_id')
apply (rule well_typed_proc_beta_reduced)
close (fact well_typed_mk_program_untyped)
by (fact Rep_program_inverse)

(*
lemma callproc:
  fixes v args q a
  assumes "subst_proc1 p q r"
  defines "q0==CallProc (mk_variable_untyped v) q (mk_procargs_untyped a)"
  shows "subst_prog1 p q0  PROGRAM[ \<guillemotleft>callproc v r a\<guillemotright> ]"
SORRY
*)




lemma callproc:
  fixes p::"'mod::procedure_functor" and q::"'mod =proc=> ('in::procargs,'out::prog_type)procedure"
        and r::"('in::procargs,'out::prog_type)procedure" and a and v::"'out variable"
  assumes qpr: "q <$> p = r"
  defines "q0 == CallProc (mk_variable_untyped v) (ProcAppl (procedure_functor_mk_untyped q) (ProcRef 0)) (mk_procargs_untyped a)"
  shows "subst_prog1 p q0 PROGRAM[ \<guillemotleft>callproc v r a\<guillemotright> ]"
proof (unfold subst_prog1_def, rule conjI)
  let ?E = "[procedure_functor_type TYPE('mod)]"
  show wt_q0: "well_typed'' ?E q0"
    unfolding q0_def 
    apply (rule well_typed''_well_typed_proc''.wt_CallProc)
     apply (rule well_typed''_well_typed_proc''.wt_ProcAppl)
     apply (insert procedure_functor_welltyped'[of "?E" "q"])[1]
     close (simp add: procedure_type_def procedure_functor_mk_untyped_procedure_ext_def)
    by (rule well_typed''_well_typed_proc''.wt_ProcRef, simp_all)

  
  have qpr': "beta_reduce (ProcAppl (procedure_functor_mk_untyped q) (procedure_functor_mk_untyped p))
            = procedure_functor_mk_untyped r"
    unfolding qpr[symmetric]
    unfolding procfun_apply_def apply_procedure_def 
    apply (subst procedure_functor_mk_typed_inverse)
     apply (rule beta_reduce_preserves_well_typed)
     apply (rule wt_ProcAppl, unfold procedure_functor_type_procedure_ext_def)
      close (rule procedure_functor_welltyped[of q, simplified])
     close (rule procedure_functor_welltyped[of p, simplified])
    by simp
  show "Abs_program (beta_reduce' (subst_proc_in_prog (0\<Colon>nat) (procedure_functor_mk_untyped p) (beta_reduce' q0))) =
    PROGRAM [ \<guillemotleft>callproc v r a\<guillemotright> ]"
    apply (subst subst_proc_beta_reduce'[where F="[]", simplified])
      close (fact wt_q0)
     close (rule procedure_functor_welltyped[of p, simplified])
    unfolding q0_def program_def callproc_def apply simp
    apply (subst beta_reduce_CallProc)
     apply (rule wt_ProcAppl)
      close (rule procedure_functor_welltyped[of q, simplified])
     close (rule procedure_functor_welltyped[of p, simplified])
    by (simp add: procedure_functor_mk_untyped_procedure_ext_def qpr')
qed

(*
lemma left: 
  assumes "subst_proc1 l q p"
  defines "q0 == ProcAppl (ProcAbs q) (ProcUnpair True (ProcRef 0))"
  shows "subst_proc1 (l, r) q0 p"
SORRY

lemma procref: 
  defines "q0 == ProcRef 0"
  shows "subst_proc1 p q0 p"
SORRY

lemma right: 
  assumes "subst_proc1 r q p"
  defines "q0 == ProcAppl (ProcAbs q) (ProcUnpair False (ProcRef 0))"
  shows "subst_proc1 (l, r) q0 p"
SORRY
*)

lemma procfun_apply:
  fixes q0 a b r a0 b0
  assumes "a0 <$> r = a"
  assumes "b0 <$> r = b"
  defines "q0 == procfun_S <$> a0 <$> b0"
  shows "q0 <$> r = a <$> b"
unfolding procfun_S assms..

lemma left:
  assumes "q <$> l = a"
  defines "q0 == procfun_compose <$> q <$> fst_procfun"
  shows "q0 <$> (l,r) = a"
by (smt assms(1) fst_conv fst_procfun procfun_compose q0_def)

lemma right:
  assumes "q <$> r = a"
  defines "q0 == procfun_compose <$> q <$> snd_procfun"
  shows "q0 <$> (l,r) = a"
by (smt assms(1) procfun_compose q0_def sndI snd_procfun)

lemma procfun_closed:
  fixes a r q0
  defines "q0 == procfun_K <$> a"
  shows "q0 <$> r = a"
by (smt procfun_K q0_def)

lemma procfun_id:
  defines "q0 == procfun_id"
  shows "q0 <$> r = r"
by (smt procfun_id q0_def)

lemmas safe = proc apply1 closed seq (*procref*) callproc
              procfun_id procfun_closed procfun_apply
lemmas unsafe = left right
lemmas reduce = safe unsafe

end

ML_file "procs_typed.ML"

(*
definition "x == Variable ''x'' :: int variable"
definition "y == Variable ''y'' :: unit variable"

(*
ML {*
structure Result = Proof_Data
(type T = unit -> (local_theory -> Proof.state)
fun init _ () = error "Result")
val result_cookie = (Result.get, Result.put, "Result.put")
*}

ML {*
  val local_setup_goal_fun = Unsynchronized.ref (fn (_:local_theory) => error "xxx" : Proof.state);
  Outer_Syntax.local_theory_to_proof @{command_spec "local_setup_goal"} 
        "invokes a 'local_theory => Proof.state' function (HACK!!!)"
        (Scan.succeed (fn x => !local_setup_goal_fun x))
*}
*)

locale test = fixes v::"(unit, unit) procedure" begin


definition_by_specification my_proc where
  "procfun_apply my_proc (p,q,r::(unit,unit)procedure) = 
     proc() { x:=1; y:=call p(); y:=call r(); return () }"

end

schematic_lemma (in reduce_procfun) l1:
  shows "\<And>p q r. my_proc == ?my_proc \<Longrightarrow> 
  (procfun_apply my_proc (p,q,r) = proc() { x:=1; y:=call p(); y:=call r(); return () })"
apply (tactic "dtac meta_eq_to_obj_eq 1")
apply (tactic "hyp_subst_tac_thin true @{context} 1")
apply (tactic "Procs_Typed.procedure_existence_tac @{context} 1")
done

(*
definition my_proc_def0: "my_proc \<equiv>
 procedure_functor_mk_typed
  (ProcAbs
    (Proc (Seq (Seq (mk_program_untyped (assign x (const_expression 1)))
                 (CallProc (mk_variable_untyped y)
                   (ProcAppl (ProcAbs (ProcRef 0)) (ProcUnpair True (ProcRef 0)))
                   (mk_procargs_untyped procargs_empty)))
            (CallProc (mk_variable_untyped y)
              (ProcAppl (ProcAbs (ProcAppl (ProcAbs (ProcRef 0)) (ProcUnpair True (ProcRef 0))))
                (ProcUnpair False (ProcRef 0)))
              (mk_procargs_untyped procargs_empty)))
      (mk_procargvars_untyped procargvars_empty) (mk_expression_untyped (const_expression ()))))"
*)

lemmas my_proc_def = my_proc_def0[THEN reduce_procfun.l1]

*)

(* TODO remove *)
named_theorems procedure_info






end

