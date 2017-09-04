theory RHL_Untyped
imports Lang_Untyped Hoare_Untyped 
begin

definition rhoare_untyped :: "(memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> program_rep \<Rightarrow> program_rep \<Rightarrow> (memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "rhoare_untyped pre c1 c2 post =
  (\<forall>m1 m2. pre m1 m2 \<longrightarrow> 
     (\<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped c1 m1
        \<and> apply_to_distr snd \<mu> = denotation_untyped c2 m2
        \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> post m1' m2')))"

definition rhoare_denotation :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "rhoare_denotation pre c1 c2 post =
  (\<forall>m1 m2. pre m1 m2 \<longrightarrow> 
     (\<exists>\<mu>. apply_to_distr fst \<mu> = c1 m1
        \<and> apply_to_distr snd \<mu> = c2 m2
        \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> post m1' m2')))"

lemma rhoare_untyped_rhoare_denotation: "rhoare_untyped pre c1 c2 post = rhoare_denotation pre (denotation_untyped c1) (denotation_untyped c2) post"
  unfolding rhoare_untyped_def rhoare_denotation_def ..

lemma rhoare_denotation_0 [simp]: "rhoare_denotation P (\<lambda>x. 0) (\<lambda>x. 0) Q"
  using apply_to_distr_0 rhoare_denotation_def by fastforce

lemma rhoare_untypedI: 
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow>
            (\<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped p1 m1 \<and>
                  apply_to_distr snd \<mu> = denotation_untyped p2 m2 \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2'))"
  shows "rhoare_untyped P p1 p2 Q"
unfolding rhoare_untyped_rhoare_denotation rhoare_denotation_def using assms by simp

lemma rhoare_untypedE: 
  assumes "rhoare_untyped P p1 p2 Q"
  assumes "P m1 m2"
  shows "\<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped p1 m1 \<and>
                  apply_to_distr snd \<mu> = denotation_untyped p2 m2 \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2')"
using assms unfolding rhoare_untyped_rhoare_denotation rhoare_denotation_def by simp



definition "assertion_footprint_left X P == (\<forall>m1 m1' m2 m2'. (\<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m1' x) \<longrightarrow> (m2::memory)=m2' \<longrightarrow> P m1 m2 = P m1' m2')"


lemma assertion_footprint_left_mono:
  assumes "X \<subseteq> Y"
  assumes "assertion_footprint_left X P"
  shows   "assertion_footprint_left Y P"
using assms unfolding assertion_footprint_left_def by blast

lemma assertion_footprint_leftI: 
  assumes "\<And>m1 m1' m2 m2'. (\<And>x. x\<in>X \<Longrightarrow> memory_lookup_untyped m1 x = memory_lookup_untyped m1' x) \<Longrightarrow> (m2::memory)=m2' \<Longrightarrow> P m1 m2 = P m1' m2'"
  shows "assertion_footprint_left X P"
unfolding assertion_footprint_left_def using assms by metis

lemma assertion_footprint_left_const: "assertion_footprint_left X (\<lambda>m. P)"
  unfolding assertion_footprint_left_def by simp
lemma assertion_footprint_left_app: "assertion_footprint_left X P \<Longrightarrow> assertion_footprint_left X Q \<Longrightarrow> assertion_footprint_left X (\<lambda>m m'. (P m m') (Q m m'))"
  unfolding assertion_footprint_left_def by force
lemma assertion_footprint_left_op2: 
  assumes "assertion_footprint_left X P"
      and "assertion_footprint_left X Q"
  shows "assertion_footprint_left X (\<lambda>m m'. f (P m m') (Q m m'))"
  using assms unfolding assertion_footprint_left_def by force
lemma assertion_footprint_left_update_pattern_untyped:
  assumes "Y \<subseteq> X \<union> set (pu_vars pat)"
  assumes "assertion_footprint_left Y P"
  shows "assertion_footprint_left X (\<lambda>m m'. P (memory_update_untyped_pattern m pat x) m')"
using assms unfolding assertion_footprint_left_def apply auto
by (smt UnE lookup_memory_update_untyped_pattern_getter memory_lookup_update_pattern_notsame subsetCE)
lemma assertion_footprint_left_map_other: 
  assumes "assertion_footprint_left X P"
  shows "assertion_footprint_left X (\<lambda>m m'. P m (f m'))"
using assms unfolding assertion_footprint_left_def by auto

lemma assertion_footprint_left_update_untyped:
  assumes "Y \<subseteq> insert x X"
  assumes "assertion_footprint_left Y P"
  shows "assertion_footprint_left X (\<lambda>m m'. P (memory_update_untyped m x v) m')"
using assms unfolding assertion_footprint_left_def apply auto
by (smt insertE memory_lookup_update_untyped subsetCE)

lemma assertion_footprint_leftE: 
  "assertion_footprint_left X P \<Longrightarrow> (\<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m1' x) \<Longrightarrow> (m2::memory)=m2' \<Longrightarrow> P m1 m2 = P m1' m2'"
unfolding assertion_footprint_left_def by simp


lemma assertion_footprint_left_forall: 
  assumes "\<And>x. assertion_footprint_left X (\<lambda>m1 m2. f x m1 m2)"
  shows "assertion_footprint_left X (\<lambda>m1 m2. \<forall>x. f x m1 m2)"
  using assms unfolding assertion_footprint_left_def by metis

lemma assertion_footprint_left_UNIV: 
  shows "assertion_footprint_left UNIV P"
    unfolding assertion_footprint_left_def
    using memory_lookup_untyped_inject[OF ext] by auto


definition "assertion_footprint_right X P == (\<forall>m1 m1' m2 m2'. (\<forall>x\<in>X. memory_lookup_untyped m2 x = memory_lookup_untyped m2' x)\<longrightarrow> (m1::memory)=m1' \<longrightarrow> P m1 m2 = P m1' m2')"
lemma assertion_footprint_right_const: "assertion_footprint_right X (\<lambda>m m'. P m)"
  unfolding assertion_footprint_right_def by simp
lemma assertion_footprint_right_app: "assertion_footprint_right X P \<Longrightarrow> assertion_footprint_right X Q \<Longrightarrow> assertion_footprint_right X (\<lambda>m m'. (P m m') (Q m m'))"
  unfolding assertion_footprint_right_def by metis

lemma assertion_footprint_right_left: "assertion_footprint_right X P = assertion_footprint_left X (\<lambda>m1 m2. P m2 m1)"
  unfolding assertion_footprint_right_def assertion_footprint_left_def by auto

lemma assertion_footprint_rightI: 
  assumes "\<And>m1 m1' m2 m2'. (\<And>x. x\<in>X \<Longrightarrow> (m1::memory)=m1' \<Longrightarrow> memory_lookup_untyped m2 x = memory_lookup_untyped m2' x) \<Longrightarrow> P m1 m2 = P m1' m2'"
  shows "assertion_footprint_right X P"
unfolding assertion_footprint_right_def using assms by (metis (mono_tags))

lemma assertion_footprint_rightE:
   "assertion_footprint_right X P \<Longrightarrow> (\<forall>x\<in>X. memory_lookup_untyped m2 x = memory_lookup_untyped m2' x) \<Longrightarrow> (m1::memory)=m1' \<Longrightarrow> P m1 m2 = P m1' m2'"
unfolding assertion_footprint_right_def by simp

lemma assertion_footprint_right_mono:
  assumes "X \<subseteq> Y"
  assumes "assertion_footprint_right X P"
  shows   "assertion_footprint_right Y P"
using assms unfolding assertion_footprint_right_def by blast

lemma assertion_footprint_right_op2: 
  assumes "assertion_footprint_right X P"
      and "assertion_footprint_right X Q"
  shows "assertion_footprint_right X (\<lambda>m m'. f (P m m') (Q m m'))"
  using assms unfolding assertion_footprint_right_def by metis
lemma assertion_footprint_right_update_pattern_untyped:
  assumes "Y \<subseteq> X \<union> set (pu_vars pat)"
  assumes "assertion_footprint_right Y P"
  shows "assertion_footprint_right X (\<lambda>m m'. P m (memory_update_untyped_pattern m' pat x))"
using assms unfolding assertion_footprint_right_def apply auto
by (smt UnE lookup_memory_update_untyped_pattern_getter memory_lookup_update_pattern_notsame subsetCE)
lemma assertion_footprint_right_map_other: 
  assumes "assertion_footprint_right X P"
  shows "assertion_footprint_right X (\<lambda>m m'. P (f m) m')"
using assms unfolding assertion_footprint_right_def by auto

lemma assertion_footprint_right_update_untyped:
  assumes "Y \<subseteq> insert x X"
  assumes "assertion_footprint_right Y P"
  shows "assertion_footprint_right X (\<lambda>m m'. P m (memory_update_untyped m' x v))"
using assms unfolding assertion_footprint_right_def apply auto
by (smt insertE memory_lookup_update_untyped subsetCE)



lemma assertion_footprint_right_forall: 
  assumes "\<And>x. assertion_footprint_right X (\<lambda>m1 m2. f x m1 m2)"
  shows "assertion_footprint_right X (\<lambda>m1 m2. \<forall>x. f x m1 m2)"
  using assms unfolding assertion_footprint_right_def by metis

lemma assertion_footprint_right_UNIV: 
  shows "assertion_footprint_right UNIV P"
    unfolding assertion_footprint_right_def
    using memory_lookup_untyped_inject[OF ext] by auto



lemma rskip_rule:
  assumes "\<forall>m1 m2. P m1 m2 \<longrightarrow> Q m1 m2"
  shows "rhoare_untyped P Skip Skip Q"
  unfolding rhoare_untyped_def apply (rule, rule, rule)
  apply (rule_tac x="point_distr (m1,m2)" in exI)
  using assms by simp

lemma rconseq_rule:
  assumes "\<forall>m1 m2. P m1 m2 \<longrightarrow> P' m1 m2"
      and "\<forall>m1 m2. Q' m1 m2 \<longrightarrow> Q m1 m2"
      and "rhoare_untyped P' c1 c2 Q'"
  shows "rhoare_untyped P c1 c2 Q"
  using assms unfolding rhoare_untyped_def by metis

lemma hoare_to_rhoare:
  assumes "lossless_untyped c"
      and h:"\<forall>m2. hoare_untyped (\<lambda>m1. P m1 m2) c (\<lambda>m1. Q m1 m2)"
  shows "rhoare_untyped P c Skip Q"
proof (unfold rhoare_untyped_def, rule, rule, rule)
  fix m1 m2 assume Pm1m2: "P m1 m2"
  define witness where "witness \<equiv> product_distr (denotation_untyped c m1) (denotation_untyped Skip m2)"
  show " \<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped c m1 \<and>
             apply_to_distr snd \<mu> = denotation_untyped Skip m2 \<and>
             (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2')"
    apply (rule exI[where x=witness])
    unfolding witness_def apply auto
    (* apply (metis scaleR_one_distr) *)
    apply (metis `lossless_untyped c` lossless_untyped_def scaleR_one_distr)
    by (metis Pm1m2 h hoare_untyped_def)
qed

lemma cong_middle: "x = x' \<Longrightarrow> f x y = f x' y" by simp

lemma rsymmetric_rule:
  assumes "rhoare_untyped (\<lambda>m1 m2. P m2 m1) c2 c1 (\<lambda>m1 m2. Q m2 m1)"
  shows "rhoare_untyped P c1 c2 Q"
proof (unfold rhoare_untyped_def, rule, rule, rule)
  fix m1 m2 assume P: "P m1 m2"
  obtain witness where wit2: "apply_to_distr fst witness = denotation_untyped c2 m2"
                   and wit1: "apply_to_distr snd witness = denotation_untyped c1 m1"
                   and correct: "\<forall>m1' m2'. (m1', m2') \<in> support_distr witness \<longrightarrow> Q m2' m1'"
       by (metis (mono_tags) P assms rhoare_untyped_def)
  define witness' where "witness' == apply_to_distr (\<lambda>(x,y). (y,x)) witness"
  have wit'1: "apply_to_distr fst witness' = denotation_untyped c1 m1"
    unfolding witness'_def wit1[symmetric] apply auto
    apply (rule cong_middle[where f=apply_to_distr])
    by auto
  have wit'2: "apply_to_distr snd witness' = denotation_untyped c2 m2"
    unfolding witness'_def wit2[symmetric] apply auto
    apply (rule cong_middle[where f=apply_to_distr])
    by auto
  also have correct': "\<forall>m1 m2. (m1, m2) \<in> support_distr witness' \<longrightarrow> Q m1 m2"
    unfolding witness'_def using correct by auto

  show "\<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped c1 m1 \<and>
                  apply_to_distr snd \<mu> = denotation_untyped c2 m2 \<and> (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2')"
    using wit'1 wit'2 correct' by auto            
qed

lemma rassign_rule1:
  assumes "\<forall>m1 m2. P m1 m2 \<longrightarrow> Q (memory_update_untyped_pattern m1 pat (eu_fun e m1)) m2"
  shows "rhoare_untyped P (Assign pat e) Skip Q"
  apply (rule hoare_to_rhoare)
  unfolding lossless_untyped_def apply simp
  apply (rule allI, rule assign_rule)
  using assms by simp

lemma rassign_rule2:
  assumes "\<forall>m1 m2. P m1 m2 \<longrightarrow> Q m1 (memory_update_untyped_pattern m2 pat (eu_fun e m2))"
  shows "rhoare_untyped P Skip (Assign pat e) Q"
apply (rule rsymmetric_rule)
apply (rule rassign_rule1)
using assms by simp

(*
lemma rnd_rule:
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>y\<in>support_distr (ed_fun e m2). y = f (f' y)"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>x\<in>support_distr (ed_fun d m1). x = f' (f x)"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>y\<in>support_distr (ed_fun e m2). prob (ed_fun e m2) y = prob (ed_fun d m1) (f' y)"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>x\<in>support_distr (ed_fun d m1). f x \<in> support_distr (ed_fun e m2)"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>x\<in>support_distr (ed_fun d m1). Q (memory_update_untyped m1 x) (memory_update_untyped m2 (f x))"
  shows "rhoare_untyped P (Sample x d) (Sample y e) Q"
*)

lemma rnd_rule:
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow> apply_to_distr fst (\<mu> m1 m2) = ed_fun d m1"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> apply_to_distr snd (\<mu> m1 m2) = ed_fun e m2"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>(xval,yval)\<in>support_distr (\<mu> m1 m2). 
           Q (memory_update_untyped_pattern m1 x xval) (memory_update_untyped_pattern m2 y yval)"
  shows "rhoare_untyped P (Sample x d) (Sample y e) Q"
  unfolding rhoare_untyped_def apply rule+ defer apply rule
proof -
  fix m1 m2 assume "P m1 m2"
  define map where "map \<equiv> \<lambda>(xval,yval). (memory_update_untyped_pattern m1 x xval, memory_update_untyped_pattern m2 y yval)"
  define \<mu>' where "\<mu>' \<equiv> apply_to_distr map (\<mu> m1 m2)"
  have mu1: "apply_to_distr fst (\<mu> m1 m2) = ed_fun d m1" using assms `P m1 m2` by simp
  have mu2: "apply_to_distr snd (\<mu> m1 m2) = ed_fun e m2" using assms `P m1 m2` by simp
  have post: "\<forall>(xval,yval)\<in>support_distr (\<mu> m1 m2).
              Q (memory_update_untyped_pattern m1 x xval) (memory_update_untyped_pattern m2 y yval)"
    using assms `P m1 m2` by simp
  show "apply_to_distr fst \<mu>' = denotation_untyped (Sample x d) m1"
    unfolding \<mu>'_def apply simp
    unfolding mu1[symmetric] apply simp
    apply (rule cong_middle[where f=apply_to_distr])
    unfolding map_def by auto
  show "apply_to_distr snd \<mu>' = denotation_untyped (Sample y e) m2" 
    unfolding \<mu>'_def apply simp
    unfolding mu2[symmetric] apply simp
    apply (rule cong_middle[where f=apply_to_distr])
    unfolding map_def by auto
  show "\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu>' \<longrightarrow> Q m1' m2'" 
    unfolding \<mu>'_def map_def using post by auto
qed


lemma rtrans_rule:
  assumes p:"\<And>m1 m2. P m1 m2 \<Longrightarrow> \<exists>m. P1 m1 m \<and> P2 m m2"
      and q:"\<And>m1 m2 m. Q1 m1 m \<Longrightarrow> Q2 m m2 \<Longrightarrow> Q m1 m2"
      and rhl1: "rhoare_untyped P1 c1 c Q1"
      and rhl2: "rhoare_untyped P2 c c2 Q2"
  shows "rhoare_untyped P c1 c2 Q"
proof (unfold rhoare_untyped_def, auto (*, rule exI, auto*))
  fix m1 m2 assume "P m1 m2"
  then obtain m where "P1 m1 m" and "P2 m m2" using p by metis
  obtain \<mu>1 where \<mu>1fst: "apply_to_distr fst \<mu>1 = denotation_untyped c1 m1"
              and \<mu>1snd: "apply_to_distr snd \<mu>1 = denotation_untyped c m"
              and \<mu>1supp: "\<And>m1' m'. (m1',m') \<in> support_distr \<mu>1 \<Longrightarrow> Q1 m1' m'"
    using `P1 m1 m` rhl1 unfolding rhoare_untyped_def by metis
  obtain \<mu>2 where \<mu>2fst: "apply_to_distr fst \<mu>2 = denotation_untyped c m"
              and \<mu>2snd: "apply_to_distr snd \<mu>2 = denotation_untyped c2 m2"
              and \<mu>2supp: "\<And>m' m2'. (m',m2') \<in> support_distr \<mu>2 \<Longrightarrow> Q2 m' m2'"
    using `P2 m m2` rhl2 unfolding rhoare_untyped_def by metis
  obtain \<mu>3 where \<mu>31: "apply_to_distr (\<lambda>(x,y,z). (x,y)) \<mu>3 = \<mu>1" 
              and \<mu>32: "apply_to_distr (\<lambda>(x,y,z). (y,z)) \<mu>3 = \<mu>2"
    using markov_chain \<mu>1snd \<mu>2fst by metis
  define \<mu> where "\<mu> \<equiv> apply_to_distr (\<lambda>(x,y,z). (x,z)) \<mu>3"
  show "\<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped c1 m1 \<and>
            apply_to_distr snd \<mu> = denotation_untyped c2 m2 \<and> 
            (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2')"
  proof (rule exI, auto)
    have tmp: "(\<lambda>x. fst (case x of (x, y, xb) \<Rightarrow> (x, xb))) = (\<lambda>(x,y,z). x)" by auto 
    show "apply_to_distr fst \<mu> = denotation_untyped c1 m1"
      unfolding \<mu>_def \<mu>1fst[symmetric] \<mu>31[symmetric] apply simp 
      by (rule cong_middle[where f=apply_to_distr], auto)
    show "apply_to_distr snd \<mu> = denotation_untyped c2 m2"
      unfolding \<mu>_def \<mu>2snd[symmetric] \<mu>32[symmetric] apply simp 
      by (rule cong_middle[where f=apply_to_distr], auto)
    fix m1' m2' assume in\<mu>: "(m1', m2') \<in> support_distr \<mu>"
    show "Q m1' m2'"
    proof -
      obtain m' where \<mu>3supp: "(m1',m',m2') \<in> support_distr \<mu>3"
        using in\<mu> unfolding \<mu>_def by auto
      from \<mu>3supp have in\<mu>1supp: "(m1',m') \<in> support_distr \<mu>1"
        unfolding \<mu>31[symmetric] by force
      from \<mu>3supp have in\<mu>2supp: "(m',m2') \<in> support_distr \<mu>2"
        unfolding \<mu>32[symmetric] by force
      show "Q m1' m2'"
        by (metis \<mu>1supp \<mu>2supp in\<mu>1supp in\<mu>2supp q)
    qed
  qed
qed

lemma rcase_rule:
  assumes "\<And>x. rhoare_untyped (\<lambda>m1 m2. P m1 m2 \<and> f m1 m2 = x) c1 c2 Q"
  shows "rhoare_untyped P c1 c2 Q"
using assms unfolding rhoare_untyped_def by metis


lemma iftrue_rule_left:
  fixes P Q I c p1 p2
  assumes "rhoare_untyped P p1 q Q"
          "\<forall>m m'. P m m' \<longrightarrow> eu_fun e m = embedding True"
  shows "rhoare_untyped P (IfTE e p1 p2) q Q"
  using assms unfolding rhoare_untyped_def by auto

lemma iffalse_rule_left:
  fixes P Q I c p1 p2
  assumes "rhoare_untyped P p2 q Q"
          "\<forall>m m'. P m m' \<longrightarrow> eu_fun e m \<noteq> embedding True"
  shows "rhoare_untyped P (IfTE e p1 p2) q Q"
  using assms unfolding rhoare_untyped_def by auto

lemma iftrue_rule_right:
  fixes P Q I c p1 p2
  assumes "rhoare_untyped P q p1 Q"
          "\<forall>m m'. P m m' \<longrightarrow> eu_fun e m' = embedding True"
  shows "rhoare_untyped P q (IfTE e p1 p2) Q"
  using assms unfolding rhoare_untyped_def by auto

lemma iffalse_rule_right:
  fixes P Q I c p1 p2
  assumes "rhoare_untyped P q p2 Q"
          "\<forall>m m'. P m m' \<longrightarrow> eu_fun e m' \<noteq> embedding True"
  shows "rhoare_untyped P q (IfTE e p1 p2) Q"
  using assms unfolding rhoare_untyped_def by auto

lemma iffalse_rule_both:
  assumes "rhoare_untyped P p2 p2' Q"
          "\<forall>m m'. P m m' \<longrightarrow> eu_fun e m \<noteq> embedding True \<and> eu_fun e' m' \<noteq> embedding True"
  shows "rhoare_untyped P (IfTE e p1 p2) (IfTE e' p1' p2') Q"
apply (rule iffalse_rule_right)
apply (rule iffalse_rule_left)
using assms by auto


lemma iftrue_rule_both:
  assumes "rhoare_untyped P p1 p1' Q"
          "\<forall>m m'. P m m' \<longrightarrow> eu_fun e m = embedding True \<and> eu_fun e' m' = embedding True"
  shows "rhoare_untyped P (IfTE e p1 p2) (IfTE e' p1' p2') Q"
apply (rule iftrue_rule_right)
apply (rule iftrue_rule_left)
using assms by auto

lemma rif_rule:
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow> eu_fun e1 m1 = eu_fun e2 m2"
  assumes "rhoare_untyped (\<lambda>m1 m2. P m1 m2 \<and> eu_fun e1 m1 = embedding True \<and> eu_fun e2 m2 = embedding True) then1 then2 Q"
  assumes "rhoare_untyped (\<lambda>m1 m2. P m1 m2 \<and> eu_fun e1 m1 \<noteq> embedding True \<and> eu_fun e2 m2 \<noteq> embedding True) else1 else2 Q"
  shows "rhoare_untyped P (IfTE e1 then1 else1) (IfTE e2 then2 else2) Q"
apply (rule rcase_rule[where f="\<lambda>m1 m2. eu_fun e1 m1 = embedding True"], rename_tac b, case_tac b)
 apply (rule iftrue_rule_both)
  close (rule rconseq_rule[OF _ _ assms(2)]; auto simp: assms(1))
 using assms(1) close auto
apply (rule iffalse_rule_both)
 close (rule rconseq_rule[OF _ _ assms(3)]; auto simp: assms(1))
using assms(1) by auto

  
lemma suminf_rhoare:
  assumes rhoare: "\<And>n::nat. rhoare_denotation P (c n) (d n) Q"
  assumes c': "\<And>x m m'. ennreal_Rep_distr (c' m) m' = (\<Sum>n. ennreal_Rep_distr (c n m) m')"
  (* assumes c': "\<And>x m m'. (\<lambda>n. ennreal_Rep_distr (c n m) m') sums (ennreal_Rep_distr (c' m) m')" *)
  assumes d': "\<And>x m m'. ennreal_Rep_distr (d' m) m' = (\<Sum>n. ennreal_Rep_distr (d n m) m')"
  shows "rhoare_denotation P c' d' Q"
proof (unfold rhoare_denotation_def, auto)
  fix m1 m2 assume P: "P m1 m2"
  (* have sumpos: "\<And>\<mu> n x. 0 \<le> (\<Sum>n'<n. ennreal_Rep_distr (\<mu> n') x)"  by (simp add: sum_nonneg) *)
  obtain \<mu>n where fst: "\<And>n. apply_to_distr fst (\<mu>n n) = (c n m1)" 
              and snd: "\<And>n. apply_to_distr snd (\<mu>n n) = (d n m2)"
              and post: "\<And>n. (\<forall>m1' m2'. (m1', m2') \<in> support_distr (\<mu>n n) \<longrightarrow> Q m1' m2')"
    apply atomize_elim using assms(1)[unfolded rhoare_denotation_def, rule_format, OF P] by metis
  have weight_\<mu>n: "\<And>n. ennreal_probability (\<mu>n n) UNIV = ennreal_probability (c n m1) UNIV"
    unfolding fst[symmetric] apply (subst ennreal_probability_apply_to_distr) by simp
  have csumbound: "\<And>n. (\<integral>\<^sup>+ x. (\<Sum>n'<n. ennreal_Rep_distr (c n' m1) x) \<partial>count_space UNIV) \<le> 1"
  proof -
    fix n 
    have "(\<integral>\<^sup>+x. (\<Sum>n'<n. ennreal_Rep_distr (c n' m1) x) \<partial>count_space UNIV)
        = (\<Sum>n'<n. (\<integral>\<^sup>+x. ennreal_Rep_distr (c n' m1) x \<partial>count_space UNIV))"
      by (subst nn_integral_sum, simp_all)
    also have "\<dots> = (\<Sum>n'<n. ennreal_probability (c n' m1) UNIV)"
      unfolding ennreal_probability_def indicator_def by auto
    also have "\<dots> \<le> (\<Sum>n'. ennreal_probability (c n' m1) UNIV)"
      by (simp add: suminf_upper_ennreal)
    also have "\<dots> = ennreal_probability (c' m1) UNIV"
      unfolding ennreal_probability_def indicator_def c' apply auto
      apply (rule nn_integral_suminf[symmetric]) by auto
    also have "\<dots> \<le> 1" by auto
    finally show "?thesis n" by assumption
  qed
  have dsumbound: "\<And>n. (\<integral>\<^sup>+ x. (\<Sum>n'<n. ennreal_Rep_distr (d n' m2) x) \<partial>count_space UNIV) \<le> 1"
  proof -
    fix n 
    have "(\<integral>\<^sup>+x. (\<Sum>n'<n. ennreal_Rep_distr (d n' m2) x) \<partial>count_space UNIV)
        = (\<Sum>n'<n. (\<integral>\<^sup>+x. ennreal_Rep_distr (d n' m2) x \<partial>count_space UNIV))"
      by (subst nn_integral_sum, simp_all)
    also have "\<dots> = (\<Sum>n'<n. ennreal_probability (d n' m2) UNIV)"
      unfolding ennreal_probability_def indicator_def by auto
    also have "\<dots> \<le> (\<Sum>n'. ennreal_probability (d n' m2) UNIV)"
      by (simp add: suminf_upper_ennreal)
    also have "\<dots> = ennreal_probability (d' m2) UNIV"
      unfolding ennreal_probability_def indicator_def d' apply auto
      apply (rule nn_integral_suminf[symmetric]) by auto
    also have "\<dots> \<le> 1" by auto
    finally show "?thesis n" by assumption
  qed
  have \<mu>nsumbound: "\<And>n. (\<integral>\<^sup>+ x. (\<Sum>n'<n. ennreal_Rep_distr (\<mu>n n') x) \<partial>count_space UNIV) \<le> 1"
  proof -
    fix n 
    have "(\<integral>\<^sup>+x. (\<Sum>n'<n. ennreal_Rep_distr (\<mu>n n') x) \<partial>count_space UNIV)
        = (\<Sum>n'<n. (\<integral>\<^sup>+x. ennreal_Rep_distr (\<mu>n n') x \<partial>count_space UNIV))"
      by (subst nn_integral_sum, simp_all)
    also have "\<dots> = (\<Sum>n'<n. ennreal_probability (\<mu>n n') UNIV)"
      unfolding ennreal_probability_def indicator_def by auto
    also have "\<dots> = (\<Sum>n'<n. ennreal_probability (c n' m1) UNIV)"
      unfolding weight_\<mu>n by simp
    also have "\<dots> \<le> (\<Sum>n'. ennreal_probability (c n' m1) UNIV)"
      by (simp add: suminf_upper_ennreal)
    also have "\<dots> = ennreal_probability (c' m1) UNIV"
      unfolding ennreal_probability_def indicator_def c' apply auto
      apply (rule nn_integral_suminf[symmetric]) by auto
    also have "\<dots> \<le> 1" by auto
    finally show "?thesis n" by assumption
  qed
  define \<mu>nsum where "\<mu>nsum \<equiv> \<lambda>n. ennreal_Abs_distr (\<lambda>m. sum (\<lambda>n'. ennreal_Rep_distr (\<mu>n n') m) {..<n})"
  have \<mu>nsum_rep: "\<And>n. ennreal_Rep_distr (\<mu>nsum n) = (\<lambda>m. sum (\<lambda>n'. ennreal_Rep_distr (\<mu>n n') m) {..<n})"
    unfolding \<mu>nsum_def using \<mu>nsumbound by (rule ennreal_Abs_distr_inverse)
  define \<mu> where "\<mu> \<equiv> SUP n::nat. \<mu>nsum n"
  define csum where "csum \<equiv> \<lambda>n. ennreal_Abs_distr (\<lambda>m. sum (\<lambda>n'. ennreal_Rep_distr (c n' m1) m) {..<n})"
  have csum_rep: "\<And>n. ennreal_Rep_distr (csum n) = (\<lambda>m. sum (\<lambda>n'. ennreal_Rep_distr (c n' m1) m) {..<n})"
    unfolding csum_def using csumbound by (rule ennreal_Abs_distr_inverse)
  define dsum where "dsum \<equiv> \<lambda>n. ennreal_Abs_distr (\<lambda>m. sum (\<lambda>n'. ennreal_Rep_distr (d n' m2) m) {..<n})"
  have dsum_rep: "\<And>n. ennreal_Rep_distr (dsum n) = (\<lambda>m. sum (\<lambda>n'. ennreal_Rep_distr (d n' m2) m) {..<n})"
    unfolding dsum_def using dsumbound by (rule ennreal_Abs_distr_inverse)
  have cinc: "incseq (\<lambda>n. csum n)"
    unfolding csum_def mono_def apply auto
    apply (subst less_eq_ennreal_Abs_distr[symmetric])
      close (rule csumbound) close (rule csumbound)
    unfolding le_fun_def apply (rule allI)
    apply (rule sum_mono2)
      by auto
  have dinc: "incseq (\<lambda>n. dsum n)"
    unfolding dsum_def mono_def apply auto
    apply (subst less_eq_ennreal_Abs_distr[symmetric])
      close (rule dsumbound) close (rule dsumbound)
    unfolding le_fun_def apply (rule allI)
    apply (rule sum_mono2)
      by auto
  have c'sup: "\<And>m. c' m1 = (SUP n. csum n)"
    apply (subst ennreal_Rep_distr_inject[symmetric])
    apply (subst ennreal_Rep_SUP_distr)
     close (rule cinc)
    unfolding csum_rep apply (subst SUP_apply[THEN ext])
    apply (subst suminf_ennreal_eq_SUP[symmetric])
    by (rule c'[THEN ext])
  have d'sup: "\<And>m. d' m2 = (SUP n. dsum n)"
    apply (subst ennreal_Rep_distr_inject[symmetric])
    apply (subst ennreal_Rep_SUP_distr)
     close (rule dinc)
    unfolding dsum_rep apply (subst SUP_apply[THEN ext])
    apply (subst suminf_ennreal_eq_SUP[symmetric])
    by (rule d'[THEN ext])
  have inc: "incseq \<mu>nsum"
    unfolding \<mu>nsum_def mono_def apply auto
    apply (subst less_eq_ennreal_Abs_distr[symmetric])
      close (rule \<mu>nsumbound) close (rule \<mu>nsumbound)
    unfolding le_fun_def apply (rule allI)
    apply (rule sum_mono2)
      by auto
  have fst0: "\<And>n. apply_to_distr fst (\<mu>nsum n) = csum n"
    apply (subst ennreal_Rep_distr_inject[symmetric]) apply (rule ext, rename_tac m)
    unfolding csum_rep apply (subst apply_to_distr_sum[symmetric, where N="{..<_}" and \<nu>=\<mu>n])
      close auto                                                                                                                                                                              
     close (simp add: \<mu>nsum_rep)
    apply (subst fst)
    apply (subst setsum_apply) by auto
  have fst': "apply_to_distr fst \<mu> = c' m1"
    unfolding \<mu>_def fst[symmetric] c'sup
    apply (subst apply_to_distr_sup)
    unfolding fst0 using inc by auto
  have snd0: "\<And>n. apply_to_distr snd (\<mu>nsum n) = dsum n"
    apply (subst ennreal_Rep_distr_inject[symmetric]) apply (rule ext, rename_tac m)
    unfolding dsum_rep apply (subst apply_to_distr_sum[symmetric, where N="{..<_}" and \<nu>=\<mu>n])
      close auto
     close (simp add: \<mu>nsum_rep)
    apply (subst snd)
    apply (subst setsum_apply) by auto
  have snd': "apply_to_distr snd \<mu> = d' m2"
    unfolding \<mu>_def fst[symmetric] d'sup
    apply (subst apply_to_distr_sup)
    unfolding snd0 using inc by auto
  have sum0: "\<And>(f::nat\<Rightarrow>ennreal) n. (\<Sum>n'<n. f n') > 0 \<Longrightarrow> \<exists>n'. f n' > 0"
  proof (rule ccontr)
    fix f::"nat\<Rightarrow>ennreal" and n assume sum:"(\<Sum>n'<n. f n') > 0" assume "\<not> (\<exists>n'. f n' > 0)"
    hence "\<And>n'. f n' \<le> 0" by (simp add: not_less)
    hence "(\<Sum>n'<n. f n') \<le> 0" by (simp add: sum_nonpos)
    with sum show False using not_le by blast
  qed
  have post'': "\<And>m1' m2' i. (m1', m2') \<in> support_distr (\<mu>nsum i) \<Longrightarrow> Q m1' m2'"
    unfolding support_distr_def' apply auto
    unfolding \<mu>nsum_rep apply (drule sum0)
    using post unfolding support_distr_def' by auto
  have post': "\<And>m1' m2'. (m1', m2') \<in> support_distr \<mu> \<Longrightarrow> Q m1' m2'"
    unfolding \<mu>_def support_distr_SUP[OF inc] using post'' by auto
  show "\<exists>\<mu>. apply_to_distr fst \<mu> = c' m1 \<and> apply_to_distr snd \<mu> = d' m2
          \<and> (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2')"
    apply (rule exI[of _ \<mu>]) using fst' snd' post' by auto
qed


(* lemma SUP_rhoare: (* TODO: is this actually true? Or could it be that the sup of the witnesses does not exist? *)
  assumes "\<And>n. rhoare_denotation P (c n) (d n) Q"
  assumes "incseq c" and "incseq d"
  shows "rhoare_denotation P (SUP n::nat. c n) (SUP n. d n) Q"
proof (unfold rhoare_denotation_def, auto)
  fix m1 m2 assume P: "P m1 m2"
  obtain \<mu>n where fst: "\<And>n. apply_to_distr fst (\<mu>n n) = (c n m1)" 
              and snd: "\<And>n. apply_to_distr snd (\<mu>n n) = (d n m2)"
              and post: "\<And>n. (\<forall>m1' m2'. (m1', m2') \<in> support_distr (\<mu>n n) \<longrightarrow> Q m1' m2')"
    apply atomize_elim using assms(1)[unfolded rhoare_denotation_def, rule_format, OF P] by metis
  define \<mu> where "\<mu> \<equiv> SUP n::nat. \<mu>n n"
  have inc: "incseq \<mu>n" (* Might not be true! *)
    by later
  hence fst': "apply_to_distr fst \<mu> = (\<Squnion>n. c n m1)"
    unfolding \<mu>_def fst[symmetric] 
    by (rule apply_to_distr_sup)
  from inc have snd': "apply_to_distr snd \<mu> = (\<Squnion>n. d n m2)"
    unfolding \<mu>_def snd[symmetric] 
    by (rule apply_to_distr_sup)
  have post': "\<And>m1' m2'. (m1', m2') \<in> support_distr \<mu> \<Longrightarrow> Q m1' m2'"
    unfolding \<mu>_def support_distr_SUP[OF inc]
    using post by auto
  show "\<exists>\<mu>. apply_to_distr fst \<mu> = (\<Squnion>n. c n m1) \<and> apply_to_distr snd \<mu> = (\<Squnion>n. d n m2)
          \<and> (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2')"
    apply (rule exI[of _ \<mu>]) using fst' snd' post' by auto
    by later
qed *)



lemma rhalt_rule [simp]: "rhoare_untyped P Halt Halt Q"
  unfolding rhoare_untyped_rhoare_denotation by simp

lemma rseq_rule_denotation: 
  assumes PcQ: "rhoare_denotation P c1 c2 Q"
  assumes QcR: "rhoare_denotation Q c1' c2' R"
  shows "rhoare_denotation P (\<lambda>m. compose_distr c1' (c1 m)) (\<lambda>m. compose_distr c2' (c2 m)) R"
proof (unfold rhoare_denotation_def, rule, rule, rule)
  fix m1 m2 assume "P m1 m2"
  with PcQ obtain \<mu> 
    where fst\<mu>: "apply_to_distr fst \<mu> = c1 m1"
    and   snd\<mu>: "apply_to_distr snd \<mu> = c2 m2"
    and   \<mu>supp: "(\<forall>(m1', m2') \<in> support_distr \<mu>. Q m1' m2')" 
      unfolding rhoare_denotation_def apply atomize_elim by blast
  obtain \<mu>0 where \<mu>0: "\<forall>m1 m2. (m1,m2)\<in>support_distr \<mu> \<longrightarrow>
          (apply_to_distr fst (\<mu>0 m1 m2) = c1' m1 \<and>
           apply_to_distr snd (\<mu>0 m1 m2) = c2' m2 \<and> 
          (\<forall>m1' m2'. (m1', m2') \<in> support_distr (\<mu>0 m1 m2) \<longrightarrow> R m1' m2'))"
    apply (atomize_elim) apply (rule choice, rule allI, rule choice, rule allI, simp)
    using QcR unfolding rhoare_denotation_def using \<mu>supp by auto
  define \<mu>' where "\<mu>' \<equiv> \<lambda>(m1,m2). \<mu>0 m1 m2"
  define \<mu>'' where "\<mu>'' \<equiv> compose_distr \<mu>' \<mu>"
  have "\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu>'' \<longrightarrow> R m1' m2'"
    apply auto unfolding \<mu>''_def Distr.support_compose_distr
    using \<mu>'_def \<mu>0 by auto
  moreover have "apply_to_distr fst \<mu>'' = compose_distr c1' (c1 m1)"
    unfolding \<mu>''_def
    unfolding Distr.compose_point_distr_l[symmetric] Distr.compose_distr_assoc[symmetric]
    unfolding Distr.compose_point_distr_l
    apply (subst compose_distr_cong[of \<mu> _ "\<lambda>(m1,m2). c1' m1"])
    close (simp add: \<mu>'_def \<mu>0 case_prod_unfold)  
    unfolding fst\<mu>[symmetric] compose_distr_apply_to_distr o_def
    by (meson case_prod_unfold)
  moreover have "apply_to_distr snd \<mu>'' = compose_distr c2' (c2 m2)"
    unfolding \<mu>''_def 
    unfolding Distr.compose_point_distr_l[symmetric] Distr.compose_distr_assoc[symmetric]
    unfolding Distr.compose_point_distr_l
    apply (subst compose_distr_cong[of \<mu> _ "\<lambda>(m1,m2). c2' m2"])
    close (simp add: \<mu>'_def \<mu>0 case_prod_unfold)  
    unfolding snd\<mu>[symmetric] compose_distr_apply_to_distr o_def
    by (meson case_prod_unfold)
  ultimately
  show "\<exists>\<mu>''. apply_to_distr fst \<mu>'' = compose_distr c1' (c1 m1) \<and>
              apply_to_distr snd \<mu>'' = compose_distr c2' (c2 m2) \<and>
              (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu>'' \<longrightarrow> R m1' m2')"
    by auto
qed


lemma rseq_rule: 
  assumes PcQ: "rhoare_untyped P c1 c2 Q"
  assumes QcR: "rhoare_untyped Q c1' c2' R"
  shows "rhoare_untyped P (Seq c1 c1') (Seq c2 c2') R"
using assms unfolding rhoare_untyped_rhoare_denotation denotation_untyped_Seq[THEN ext]
by (rule rseq_rule_denotation)
(*
proof (unfold rhoare_untyped_def, rule, rule, rule)
  fix m1 m2 assume "P m1 m2"
  with PcQ obtain \<mu> 
    where fst\<mu>: "apply_to_distr fst \<mu> = denotation_untyped c1 m1"
    and   snd\<mu>: "apply_to_distr snd \<mu> = denotation_untyped c2 m2"
    and   \<mu>supp: "(\<forall>(m1', m2') \<in> support_distr \<mu>. Q m1' m2')" 
      unfolding rhoare_untyped_def apply atomize_elim by blast
  obtain \<mu>0 where \<mu>0: "\<forall>m1 m2. (m1,m2)\<in>support_distr \<mu> \<longrightarrow>
          (apply_to_distr fst (\<mu>0 m1 m2) = denotation_untyped c1' m1 \<and>
           apply_to_distr snd (\<mu>0 m1 m2) = denotation_untyped c2' m2 \<and> 
          (\<forall>m1' m2'. (m1', m2') \<in> support_distr (\<mu>0 m1 m2) \<longrightarrow> R m1' m2'))"
    apply (atomize_elim) apply (rule choice, rule allI, rule choice, rule allI, simp)
    using QcR unfolding rhoare_untyped_def using \<mu>supp by auto
  define \<mu>' where "\<mu>' \<equiv> \<lambda>(m1,m2). \<mu>0 m1 m2"
  define \<mu>'' where "\<mu>'' \<equiv> compose_distr \<mu>' \<mu>"
  have "\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu>'' \<longrightarrow> R m1' m2'"
    apply auto unfolding \<mu>''_def Distr.support_compose_distr
    using \<mu>'_def \<mu>0 by auto
  moreover have "apply_to_distr fst \<mu>'' = denotation_untyped (Seq c1 c1') m1"
    unfolding \<mu>''_def apply simp 
    unfolding Distr.compose_point_distr_l[symmetric] Distr.compose_distr_assoc[symmetric]
    unfolding Distr.compose_point_distr_l
    apply (subst compose_distr_cong[of \<mu> _ "\<lambda>(m1,m2). denotation_untyped c1' m1"])
    close (simp add: \<mu>'_def \<mu>0 case_prod_unfold)  
    unfolding fst\<mu>[symmetric] compose_distr_apply_to_distr o_def
    by (meson case_prod_unfold)
  moreover have "apply_to_distr snd \<mu>'' = denotation_untyped (Seq c2 c2') m2"
    unfolding \<mu>''_def apply simp 
    unfolding Distr.compose_point_distr_l[symmetric] Distr.compose_distr_assoc[symmetric]
    unfolding Distr.compose_point_distr_l
    apply (subst compose_distr_cong[of \<mu> _ "\<lambda>(m1,m2). denotation_untyped c2' m2"])
    close (simp add: \<mu>'_def \<mu>0 case_prod_unfold)  
    unfolding snd\<mu>[symmetric] compose_distr_apply_to_distr o_def
    by (meson case_prod_unfold)
  ultimately
  show "\<exists>\<mu>''. apply_to_distr fst \<mu>'' = denotation_untyped (Seq c1 c1') m1 \<and>
              apply_to_distr snd \<mu>'' = denotation_untyped (Seq c2 c2') m2 \<and>
              (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu>'' \<longrightarrow> R m1' m2')"
    by auto
qed
*)


lemma rwhile_rule:
  assumes hoare: "rhoare_untyped (\<lambda>m1 m2. I m1 m2 \<and> eu_fun e1 m1 = embedding True) p1 p2 I"
      and PI: "\<And>m1 m2. P m1 m2 \<Longrightarrow> I m1 m2"
      and Ieq: "\<And>m1 m2. I m1 m2 \<Longrightarrow> eu_fun e1 m1 = eu_fun e2 m2"
      and IQ: "\<And>m1 m2. eu_fun e1 m1 \<noteq> embedding True \<Longrightarrow> eu_fun e2 m2 \<noteq> embedding True \<Longrightarrow> I m1 m2 \<Longrightarrow> Q m1 m2"
  shows "rhoare_untyped P (While e1 p1) (While e2 p2) Q"
proof -
  {fix n have "rhoare_untyped I (While_n_exact n e1 p1) (While_n_exact n e2 p2) Q"
  proof (induction n)
  case 0 
    show ?case 
      apply simp apply (rule rif_rule)
        using Ieq close simp
       close simp
      apply (rule rskip_rule)
       using IQ by simp
  case (Suc n)
    have preserve: "rhoare_untyped (\<lambda>m1 m2. I m1 m2 \<and> eu_fun e1 m1 = embedding True \<and> eu_fun e2 m2 = embedding True) 
              (Seq p1 (While_n_exact n e1 p1)) (Seq p2 (While_n_exact n e2 p2)) Q"
      apply (rule rseq_rule[where Q=I])
       apply (rule rconseq_rule[rotated -1])
         close (fact hoare)
        close simp close simp
      by (fact Suc.IH) 
    have exit: "rhoare_untyped (\<lambda>m1 m2. I m1 m2 \<and> eu_fun e1 m1 \<noteq> embedding True \<and> eu_fun e2 m2 \<noteq> embedding True) Halt Halt Q"
      by simp
    show ?case
      apply simp
      using Ieq preserve exit by (rule rif_rule)
  qed}
  hence nsteps: "\<And>n. rhoare_untyped P (While_n_exact n e1 p1) (While_n_exact n e2 p2) Q"
    apply (rule rconseq_rule[rotated -1])
    using PI by simp_all
  show ?thesis
    unfolding rhoare_untyped_rhoare_denotation 
    apply (rule suminf_rhoare)
      close (rule nsteps[unfolded rhoare_untyped_rhoare_denotation])      
     close (rule denotation_untyped_While'')
    by (rule denotation_untyped_While'')
qed


(* lemma rwhile_rule:
  assumes hoare: "rhoare_untyped (\<lambda>m1 m2. I m1 m2 \<and> eu_fun e1 m1 = embedding True) p1 p2 I"
      and PI: "\<And>m1 m2. P m1 m2 \<Longrightarrow> I m1 m2"
      and Ieq: "\<And>m1 m2. I m1 m2 \<Longrightarrow> eu_fun e1 m1 = eu_fun e2 m2"
      and IQ: "\<And>m1 m2. eu_fun e1 m1 \<noteq> embedding True \<Longrightarrow> eu_fun e2 m2 \<noteq> embedding True \<Longrightarrow> I m1 m2 \<Longrightarrow> Q m1 m2"
  shows "rhoare_untyped P (While e1 p1) (While e2 p2) Q"
proof -
  {fix n have "rhoare_untyped I (While_n n e1 p1) (While_n n e2 p2) Q"
  proof (induction n)
  case 0 show ?case by simp
  case (Suc n)
    have preserve: "rhoare_untyped (\<lambda>m1 m2. I m1 m2 \<and> eu_fun e1 m1 = embedding True \<and> eu_fun e2 m2 = embedding True) 
              (Seq p1 (While_n n e1 p1)) (Seq p2 (While_n n e2 p2)) Q"
      apply (rule rseq_rule[where Q=I])
       apply (rule rconseq_rule[rotated -1])
         close (fact hoare)
        close simp close simp
      by (fact Suc.IH) 
    have exit: "rhoare_untyped (\<lambda>m1 m2. I m1 m2 \<and> eu_fun e1 m1 \<noteq> embedding True \<and> eu_fun e2 m2 \<noteq> embedding True) Skip Skip Q"
      apply (rule rskip_rule) using IQ by simp
    show ?case
      apply simp
      using Ieq preserve exit by (rule rif_rule)
  qed}
  hence "\<And>n. rhoare_untyped P (While_n n e1 p1) (While_n n e2 p2) Q"
    apply (rule rconseq_rule[rotated -1])
    using PI by simp_all
  thus ?thesis
    unfolding rhoare_untyped_rhoare_denotation denotation_untyped_While'
    by (rule SUP_rhoare) 
qed *)


(*definition "blockassign (xs::variable_untyped list) (es::expression_untyped list) == 
  fold (\<lambda>(x,e) p. Seq p (Assign x e)) (zip xs es) Skip"*)

definition "obs_eq_untyped X Y c1 c2 ==
  rhoare_untyped (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)
                 c1 c2
                 (\<lambda>m1 m2. \<forall>x\<in>Y. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"

lemma rhoare_denotation_post_eq: 
  fixes X c1 c2 P
  defines "project == (\<lambda>m x. if x\<in>X then memory_lookup_untyped m x else undefined)"
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow> apply_to_distr project (c1 m1) = apply_to_distr project (c2 m2)"
  shows "rhoare_denotation P c1 c2 (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
proof (unfold rhoare_denotation_def, auto del: exI intro!: exI )
  fix m1 m2 
  assume P: "P m1 m2"
  define project_other where "project_other \<equiv> (\<lambda>m x. if x\<notin>X then memory_lookup_untyped m x else undefined)"
  define \<mu>1 where "\<mu>1 \<equiv> apply_to_distr (\<lambda>m. (project_other m, project m)) (c1 m1)"
  define \<mu>2 where "\<mu>2 \<equiv> apply_to_distr (\<lambda>m. (project m, project_other m)) (c2 m2)"
  have \<mu>1\<mu>2: "apply_to_distr snd \<mu>1 = apply_to_distr fst \<mu>2"
    unfolding \<mu>1_def \<mu>2_def using P assms(2) by auto
  define \<mu>' where "\<mu>' \<equiv> markov_chain_combine \<mu>1 \<mu>2"
  have \<mu>1: "apply_to_distr (\<lambda>(x,y,z). (x,y)) \<mu>' = \<mu>1" 
    using \<mu>1\<mu>2 unfolding \<mu>'_def \<mu>1_def \<mu>2_def by (rule markov_chain)
  have \<mu>2: "apply_to_distr (\<lambda>(x,y,z). (y,z)) \<mu>' = \<mu>2"
    using \<mu>1\<mu>2 unfolding \<mu>'_def \<mu>1_def \<mu>2_def by (rule markov_chain)

  define recon1 where "recon1 \<equiv> (\<lambda>(m,m'). Abs_memory (\<lambda>x. if x\<notin>X then m x else m' x))"
  have "(\<lambda>x. (\<lambda>(m,m') x. if x\<notin>X then m x else m' x) (project_other x, project x)) = Rep_memory"
    unfolding recon1_def project_other_def project_def by force
  hence "\<And>x. recon1 (project_other x, project x) = x"
    by (metis (no_types, lifting) Rep_memory_inverse recon1_def split_conv)
  hence recon1: "apply_to_distr recon1 \<mu>1 = c1 m1"
    unfolding \<mu>1_def by auto

  define recon2 where "recon2 \<equiv> (\<lambda>(m,m'). Abs_memory (\<lambda>x. if x\<in>X then m x else m' x))"
  have "(\<lambda>x. (\<lambda>(m,m') x. if x\<in>X then m x else m' x) (project x, project_other x)) = Rep_memory"
    unfolding recon1_def project_other_def project_def by force
  hence "\<And>x. recon2 (project x, project_other x) = x"
    by (metis (no_types, lifting) Rep_memory_inverse recon2_def split_conv)
  hence recon2: "apply_to_distr recon2 \<mu>2 = c2 m2"
    unfolding \<mu>2_def by auto

  define \<mu> where "\<mu> \<equiv> apply_to_distr (\<lambda>(x,y,z). (recon1 (x,y), recon2 (y,z))) \<mu>'"
  have "apply_to_distr fst \<mu> = apply_to_distr (\<lambda>(x, y, z). recon1 (x, y)) \<mu>'"
    unfolding \<mu>_def apply simp
    apply (tactic \<open>cong_tac @{context} 1\<close>, tactic \<open>cong_tac @{context} 1\<close>) by auto
  also have "\<dots> = apply_to_distr recon1 \<mu>1"
    unfolding \<mu>1[symmetric] apply simp
    apply (tactic \<open>cong_tac @{context} 1\<close>, tactic \<open>cong_tac @{context} 1\<close>) by auto
  also have "\<dots> = c1 m1"
    by (fact recon1)
  finally show "apply_to_distr fst \<mu> = c1 m1"
    by assumption

  have "apply_to_distr snd \<mu> = apply_to_distr (\<lambda>(x, y, z). recon2 (y, z)) \<mu>'"
    unfolding \<mu>_def apply simp
    apply (tactic \<open>cong_tac @{context} 1\<close>, tactic \<open>cong_tac @{context} 1\<close>) by auto
  also have "\<dots> = apply_to_distr recon2 \<mu>2"
    unfolding \<mu>2[symmetric] apply simp
    apply (tactic \<open>cong_tac @{context} 1\<close>, tactic \<open>cong_tac @{context} 1\<close>) by auto
  also have "\<dots> = c2 m2"
    by (fact recon2)
  finally show "apply_to_distr snd \<mu> = c2 m2"
    by assumption

  fix m1' m2' x
  assume "(m1', m2') \<in> support_distr \<mu>"
  then obtain a b c where m1': "m1' = recon1 (a,b)" and m2': "m2' = recon2 (b,c)"
    and supp_abc: "(a,b,c) \<in> support_distr \<mu>'"
    unfolding \<mu>_def by auto
  have supp_ab: "(a,b) \<in> support_distr \<mu>1" and supp_bc: "(b,c) \<in> support_distr \<mu>2"
    using \<mu>1\<mu>2 supp_abc unfolding \<mu>'_def apply (rule markov_chain_support)
    using \<mu>1\<mu>2 supp_abc unfolding \<mu>'_def by (rule markov_chain_support)
  from supp_ab obtain mab where a: "a = project_other mab" and b: "b = project mab"
    unfolding \<mu>1_def by auto
  from supp_bc obtain mbc where c: "c = project_other mbc"
    unfolding \<mu>2_def by auto
  have RepAbs_ab: "Rep_memory (Abs_memory (\<lambda>x. if x \<notin> X then a x else b x)) = (\<lambda>x. if x \<notin> X then a x else b x)"
    apply (subst Abs_memory_inverse)
     by (simp_all add: a b project_other_def project_def)
  have RepAbs_bc: "Rep_memory (Abs_memory (\<lambda>x. if x \<in> X then b x else c x)) = (\<lambda>x. if x \<in> X then b x else c x)"
    apply (subst Abs_memory_inverse)
     by (simp_all add: b c project_other_def project_def)

  assume "x \<in> X"
  thus "memory_lookup_untyped m1' x = memory_lookup_untyped m2' x"
    unfolding m1' m2' recon1_def recon2_def using RepAbs_ab RepAbs_bc by auto
qed

lemma rhoare_denotation_post_eq2: 
  fixes X c1 c2 P
  defines "project == (\<lambda>m x. if x\<in>X then memory_lookup_untyped m x else undefined)"
  assumes rhoare: "rhoare_denotation P c1 c2 (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
  shows "\<And>m1 m2. P m1 m2 \<Longrightarrow> apply_to_distr project (c1 m1) = apply_to_distr project (c2 m2)"
proof -
  fix m1 m2 assume P: "P m1 m2"
  from rhoare obtain \<mu> where \<mu>c1: "apply_to_distr fst \<mu> = c1 m1" and \<mu>c2: "apply_to_distr snd \<mu> = c2 m2"
     and eq: "\<And>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<Longrightarrow> (\<forall>x\<in>X. memory_lookup_untyped m1' x = memory_lookup_untyped m2' x)"
    unfolding rhoare_denotation_def using P by force
  from eq have project_eq: "\<And>x. x \<in> support_distr \<mu> \<Longrightarrow> project (fst x) = project (snd x)"
    unfolding project_def by force

  have "apply_to_distr project (c1 m1) = apply_to_distr (\<lambda>m. project (fst m)) \<mu>"
    unfolding \<mu>c1[symmetric] by simp
  also have "\<dots> = apply_to_distr (\<lambda>m. project (snd m)) \<mu>"
    by (rule apply_to_distr_cong, fact project_eq)
  also have "\<dots> = apply_to_distr project (c2 m2)"
    unfolding \<mu>c2[symmetric] by simp
  finally show "apply_to_distr project (c1 m1) = apply_to_distr project (c2 m2)"
    by assumption
qed

(*
lemma obs_eq_untypedI: 
  fixes X c1 c2
  defines "project == (\<lambda>m x. if x\<in>X then memory_lookup_untyped m x else undefined)"
  assumes "\<And>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x
            \<Longrightarrow> apply_to_distr project (denotation_untyped c1 m1)
              = apply_to_distr project (denotation_untyped c2 m2)"
  shows "obs_eq_untyped X c1 c2"
unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation
apply (rule rhoare_denotation_post_eq)
using assms by auto
*)

lemma obs_eq_untyped_sym: 
  assumes "obs_eq_untyped X Y c d"
  shows "obs_eq_untyped X Y d c"
unfolding obs_eq_untyped_def
apply (rule rsymmetric_rule)
apply (subst (1) eq_commute)
apply (subst (2) eq_commute)
using assms unfolding obs_eq_untyped_def by assumption

lemma obseq_mono1: 
  assumes "X' \<ge> X"
  assumes "obs_eq_untyped X Y c d"
  shows "obs_eq_untyped X' Y c d"
by (smt assms(1) assms(2) obs_eq_untyped_def rconseq_rule set_mp)

lemma obseq_mono2: 
  assumes "Y' \<le> Y"
  assumes "obs_eq_untyped X Y c d"
  shows "obs_eq_untyped X Y' c d"
by (smt assms(1) assms(2) in_mono obs_eq_untyped_def rhoare_untyped_def)

lemma self_obseq_assign:
  assumes "set (eu_vars e) \<subseteq> X"
  assumes "Y \<subseteq> X\<union>set(pu_vars x)"
  shows "obs_eq_untyped X Y (Assign x e) (Assign x e)"
proof -
  define eq where "eq \<equiv> \<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  define eqY where "eqY \<equiv> \<lambda>m1 m2. \<forall>x\<in>Y. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  have em1m2: "\<And>m1 m2. eq m1 m2 \<Longrightarrow> eu_fun e m1 = eu_fun e m2"
    by (meson assms(1) eu_fun_footprint local.eq_def subsetCE)
  have eqYupd: "\<And>m1 m2 z. eq m1 m2 \<Longrightarrow> eqY (memory_update_untyped_pattern m1 x z) (memory_update_untyped_pattern m2 x z)"
  proof (auto simp: eqY_def)
    fix m1 m2 z y assume yY: "y \<in> Y" and eq: "eq m1 m2"
    show "memory_lookup_untyped (memory_update_untyped_pattern m1 x z) y
        = memory_lookup_untyped (memory_update_untyped_pattern m2 x z) y"
    proof (cases "y \<in> set(pu_vars x)")
    case True show ?thesis
      apply (subst lookup_memory_update_untyped_pattern_getter)
       close (fact True)
      apply (subst lookup_memory_update_untyped_pattern_getter)
       close (fact True)
      by simp
    next case False 
      hence yX: "y \<in> X" using yY assms(2) by auto
      show ?thesis
      apply (subst memory_lookup_update_pattern_notsame)
       close (fact False)
      apply (subst memory_lookup_update_pattern_notsame)
       close (fact False)
      using yX eq eq_def by auto
    qed
  qed
  have "rhoare_untyped eq (Seq (Assign x e) Skip) (Seq Skip (Assign x e)) eqY"
    apply (rule rseq_rule[rotated])
     unfolding eq_def close (rule rassign_rule2, rule allI, rule allI, rule imp_refl)
    apply (rule rassign_rule1, auto)
    apply (subst em1m2)
     unfolding eq_def close assumption
    apply (rule eqYupd)
    unfolding eq_def by assumption 
  thus ?thesis
    unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation eq_def eqY_def by simp
qed

lemma tmp: (* TODO hide / rename *)
  assumes bodyX: "set (vars_untyped body) \<subseteq> X \<union> {x. \<not> vu_global x}"
  assumes retX: "set (eu_vars ret) \<subseteq> X \<union> {x. \<not> vu_global x}"
  assumes argsX: "set (pu_vars args) \<subseteq> X \<union> {x. \<not> vu_global x}"
  assumes aX: "set (eu_vars a) \<subseteq> X"
  assumes hyps: "\<And>X. set (vars_untyped body) \<subseteq> X \<Longrightarrow> obs_eq_untyped X X body body"
  shows "obs_eq_untyped X (X \<union> set (pu_vars x)) (CallProc x (Proc body args ret) a) (CallProc x (Proc body args ret) a)"
proof -
  define X' where "X' \<equiv> X \<union> {x. \<not> vu_global x}"
  define Y where "Y \<equiv> X \<union> set (pu_vars x)"
  have eq_body: "obs_eq_untyped X' X' body body"
    using bodyX X'_def hyps by simp

  have deneq: "\<And>m1 m2. (\<And>x. x\<in>X \<Longrightarrow> memory_lookup_untyped m1 x = memory_lookup_untyped m2 x) \<Longrightarrow>
          (\<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped (CallProc x (Proc body args ret) a) m1 \<and>
                apply_to_distr snd \<mu> = denotation_untyped (CallProc x (Proc body args ret) a) m2 \<and>
                (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu> \<longrightarrow> (\<forall>x\<in>Y. memory_lookup_untyped m1' x = memory_lookup_untyped m2' x)))"
  proof -
    fix m1 m2 assume eq: "\<And>x. x\<in>X \<Longrightarrow> memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
    define d1 where "d1 \<equiv> denotation_untyped (CallProc x (Proc body args ret) a) m1"
    define d2 where "d2 \<equiv> denotation_untyped (CallProc x (Proc body args ret) a) m2"

    define argval where "argval \<equiv> eu_fun a m1"
    define m'1 where "m'1 \<equiv> init_locals m1"
    define m''1 where "m''1 \<equiv> memory_update_untyped_pattern m'1 args argval"
    define post1 where "post1 \<equiv> \<lambda>m'. let res = eu_fun ret m'; m' = restore_locals m1 m' in memory_update_untyped_pattern m' x res"
    have d1: "d1 = apply_to_distr post1 (denotation_untyped body m''1)"
      unfolding d1_def denotation_untyped_CallProc m''1_def argval_def m'1_def post1_def by simp

    have argval2: "argval = eu_fun a m2"
      using eq unfolding argval_def 
      apply (rule Lang_Untyped.eu_fun_footprint)
      using aX by auto
    define m'2 where "m'2 \<equiv> init_locals m2"
    define m''2 where "m''2 \<equiv> memory_update_untyped_pattern m'2 args argval"
    define post2 where "post2 \<equiv> (\<lambda>m'. let res = eu_fun ret m'; m' = restore_locals m2 m' in memory_update_untyped_pattern m' x res)"
    have d2: "d2 = apply_to_distr post2 (denotation_untyped body m''2)"
      unfolding d2_def denotation_untyped_CallProc m''2_def argval2 m'2_def post2_def by simp

    have m'eq: "\<And>x. x\<in>X' \<Longrightarrow> memory_lookup_untyped m'1 x = memory_lookup_untyped m'2 x"
      unfolding X'_def m'1_def m'2_def Rep_init_locals using eq by auto

    hence m''eq: "\<And>x. x\<in>X' \<Longrightarrow> memory_lookup_untyped m''1 x = memory_lookup_untyped m''2 x"
      unfolding m''1_def m''2_def
      apply (rule memory_update_untyped_pattern_footprint[where X=X'])
      unfolding X'_def using argsX by auto 

    obtain \<mu>0 where \<mu>0fst: "apply_to_distr fst \<mu>0 = denotation_untyped body m''1" and
                    \<mu>0snd: "apply_to_distr snd \<mu>0 = denotation_untyped body m''2" and
                    \<mu>0eq: "\<And>m1' m2'. (m1', m2') \<in> support_distr \<mu>0 \<Longrightarrow> (\<forall>x\<in>X'. memory_lookup_untyped m1' x = memory_lookup_untyped m2' x)"
      apply atomize_elim
      apply (rule eq_body[unfolded obs_eq_untyped_def rhoare_untyped_rhoare_denotation rhoare_denotation_def, rule_format])
      by (rule m''eq)

    define \<mu> where "\<mu> \<equiv> apply_to_distr (\<lambda>(m1,m2). (post1 m1, post2 m2)) \<mu>0"
    have \<mu>d1: "apply_to_distr fst \<mu> = d1"
      unfolding \<mu>_def d1 \<mu>0fst[symmetric] apply simp
      apply (rule apply_to_distr_cong) by auto
    have \<mu>d2: "apply_to_distr snd \<mu> = d2"
      unfolding \<mu>_def d2 \<mu>0snd[symmetric] apply simp
      apply (rule apply_to_distr_cong) by auto

    have eq_after: "\<And>m1' m2' x. (m1', m2') \<in> support_distr \<mu> \<Longrightarrow> x\<in>Y \<Longrightarrow> memory_lookup_untyped m1' x = memory_lookup_untyped m2' x"
    proof - 
      fix m1' m2' assume "(m1', m2') \<in> support_distr \<mu>"
      then obtain m1'' m2'' where supp'': "(m1'',m2'')\<in>support_distr \<mu>0" and m1'': "m1'=post1 m1''" and m2'': "m2'=post2 m2''"
        unfolding \<mu>_def by auto
      from supp'' have eq'': "\<And>x. x\<in>X' \<Longrightarrow> memory_lookup_untyped m1'' x = memory_lookup_untyped m2'' x"
        using \<mu>0eq by blast
      define res where "res \<equiv> eu_fun ret m1''"
      have res2: "res = eu_fun ret m2''"
        unfolding res_def apply (rule eu_fun_footprint) using retX eq'' unfolding X'_def by auto
      define m1a where "m1a \<equiv> restore_locals m1 m1''"
      define m2a where "m2a \<equiv> restore_locals m2 m2''"
      have m1a: "m1' = memory_update_untyped_pattern m1a x res"
        by (simp add: m1'' m1a_def post1_def res_def)
      have m2a: "m2' = memory_update_untyped_pattern m2a x res"
        by (simp add: m2'' m2a_def post2_def res2)
      have eqa: "\<And>x. x\<in>X \<Longrightarrow> memory_lookup_untyped m1a x = memory_lookup_untyped m2a x"
        unfolding m1a_def m2a_def Rep_restore_locals using eq eq'' X'_def by auto
      show "x\<in>Y \<Longrightarrow> memory_lookup_untyped m1' x = memory_lookup_untyped m2' x" for x
        unfolding m1a m2a unfolding Y_def
        apply (cases "x\<in>X")
        apply (rule memory_update_untyped_pattern_footprint_STRONGER[where X=X]) 
          using eqa close 2
        by (simp add: lookup_memory_update_untyped_pattern_getter)
    qed

    show "\<exists>\<mu>. apply_to_distr fst \<mu> = d1 \<and> apply_to_distr snd \<mu> = d2 \<and>
              (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu> \<longrightarrow> (\<forall>x\<in>Y. memory_lookup_untyped m1' x = memory_lookup_untyped m2' x))"
      apply (rule exI[of _ \<mu>]) using \<mu>d1 \<mu>d2 eq_after by auto
  qed
  show ?thesis
    unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation rhoare_denotation_def
    using deneq unfolding Y_def by auto
qed


lemma self_obseq_vars_untyped:
  assumes vars: "set(vars_untyped c) \<subseteq> X"
  assumes YX: "Y \<subseteq> X"
  shows "obs_eq_untyped X Y c c"
proof -
  fix x p a
  have "set(vars_untyped c) \<subseteq> X \<Longrightarrow> obs_eq_untyped X X c c"
   and "set(vars_untyped (CallProc x p a)) \<subseteq> X
        \<Longrightarrow> obs_eq_untyped X X (CallProc x p a) (CallProc x p a)"
  proof (induct c and p arbitrary: X and X x a)
  case (Assign x e)
    show ?case apply (rule self_obseq_assign)
      using Assign by auto
  next case (Sample x e) 
    define eq where "eq \<equiv> \<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
    define \<mu> where "\<mu> \<equiv> \<lambda>m1 m2::memory. apply_to_distr (\<lambda>x. (x,x)) (ed_fun e m1)"
    have fstsnd: "\<And>m1 m2. apply_to_distr fst (\<mu> m1 m2) = apply_to_distr snd (\<mu> m1 m2)"
      unfolding \<mu>_def by simp
    have eX: "set (ed_vars e) \<subseteq> X"
      using Sample by simp
    have em1: "\<And>m1 m2. apply_to_distr fst (\<mu> m1 m2) = ed_fun e m1"
      unfolding \<mu>_def by simp
    moreover have "\<And>m1 m2. eq m1 m2 \<Longrightarrow> apply_to_distr snd (\<mu> m1 m2) = ed_fun e m2" 
      unfolding fstsnd[symmetric] em1 eq_def apply (rule ed_fun_footprint) using eX by auto
    moreover have "\<And>m1 m2. eq m1 m2 \<Longrightarrow> \<forall>(xval, yval)\<in>support_distr (\<mu> m1 m2).
                \<forall>y\<in>X. memory_lookup_untyped (memory_update_untyped_pattern m1 x xval) y =
                       memory_lookup_untyped (memory_update_untyped_pattern m2 x yval) y"
    proof auto
      fix m1 m2 xval yval y assume yX: "y \<in> X" assume eq: "eq m1 m2"
      assume "(xval, yval)\<in>support_distr (\<mu> m1 m2)" 
      hence xyval: "xval = yval"
        unfolding \<mu>_def by auto
      thus "memory_lookup_untyped (memory_update_untyped_pattern m1 x xval) y 
          = memory_lookup_untyped (memory_update_untyped_pattern m2 x yval) y"
      proof (cases "y \<in> set(pu_vars x)")
      case True
        show ?thesis
          unfolding xyval 
          apply (rule memory_update_untyped_pattern_footprint[where X=X])
          using eq eq_def close auto
          using Sample close simp
          using yX by simp 
      next case False
        show ?thesis
          apply (subst memory_lookup_update_pattern_notsame[OF False])
          apply (subst memory_lookup_update_pattern_notsame[OF False])
          using eq yX unfolding eq_def by blast
      qed
    qed
    ultimately show ?case
      unfolding obs_eq_untyped_def eq_def 
      by (rule rnd_rule[where \<mu>=\<mu>])
  next case Seq thus ?case
    by (smt Un_upper2 dual_order.trans obs_eq_untyped_def rseq_rule set_append sup_ge1 vars_untyped.simps(2))
  next case Skip thus ?case
    using obs_eq_untyped_def rskip_rule by auto
  next case (IfTE b c1 c2)
    have "set (vars_untyped c1) \<subseteq> X"
      using IfTE.prems by auto
    hence rh_c1: "rhoare_untyped (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x) c1 c1
                          (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
      using IfTE.hyps unfolding obs_eq_untyped_def by blast
    have "set (vars_untyped c2) \<subseteq> X"
      using IfTE.prems by auto
    hence rh_c2: "rhoare_untyped (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x) c2 c2
                          (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
      using IfTE.hyps unfolding obs_eq_untyped_def by blast
    show ?case
      unfolding obs_eq_untyped_def
      apply (rule rif_rule) 
        close (metis IfTE.prems Un_upper1 eu_fun_footprint set_append subsetCE vars_untyped.simps(5)) 
       close (rule rconseq_rule[OF _ _ rh_c1]; simp)
      by (rule rconseq_rule[OF _ _ rh_c2]; simp)
  next case (While b c X)
    let ?I = "\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
    have rh: "rhoare_untyped (\<lambda>m1 m2. (\<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x) \<and> eu_fun b m1 = embedding True) c c
     (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
      apply (rule rconseq_rule[rotated -1])
        using While unfolding obs_eq_untyped_def by auto
    show ?case
      unfolding obs_eq_untyped_def
      apply (rule rwhile_rule[where I="?I"])
         close (fact rh)
        apply auto
      by (metis (full_types) While.prems eu_fun_footprint set_append set_rev_mp sup_ge1 vars_untyped.simps(6))
  next case CallProc thus ?case by blast 
  next case (Proc body args ret) 
    show ?case 
      apply (rule RHL_Untyped.obseq_mono2[rotated])
      apply (rule tmp) using Proc by auto
  next case ProcRef show ?case
    unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation
    unfolding denotation_untyped_CallProc_bad[THEN ext]
    by simp
  next case ProcAbs show ?case 
    unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation
    unfolding denotation_untyped_CallProc_bad[THEN ext]
    by simp
  next case ProcAppl show ?case 
    unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation
    unfolding denotation_untyped_CallProc_bad[THEN ext]
    by simp
  next case ProcPair show ?case 
    unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation
    unfolding denotation_untyped_CallProc_bad[THEN ext]
    by simp
  next case ProcUnpair show ?case 
    unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation
    unfolding denotation_untyped_CallProc_bad[THEN ext]
    by simp
  next case ProcUnit show ?case 
    unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation
    unfolding denotation_untyped_CallProc_bad[THEN ext]
    by simp
  qed
  hence "obs_eq_untyped X X c c"
    using vars by simp
  with YX show ?thesis
    by (rule obseq_mono2)
qed

lemma self_obs_eq_callproc_untyped:
  assumes YX: "Y \<subseteq> X \<union> set (pu_vars x)"
  assumes bodyX: "set (vars_untyped body) \<subseteq> X \<union> {x. \<not> vu_global x}"
  assumes retX: "set (eu_vars ret) \<subseteq> X \<union> {x. \<not> vu_global x}"
  assumes argsX: "set (pu_vars args) \<subseteq> X \<union> {x. \<not> vu_global x}"
  assumes aX: "set (eu_vars y) \<subseteq> X"
  shows "obs_eq_untyped X Y (CallProc x (Proc body args ret) y) (CallProc x (Proc body args ret) y)"
    apply (rule RHL_Untyped.obseq_mono2[where Y="X \<union> set (pu_vars x)"])
     using assms close
    apply (rule tmp)
        using assms close 4
    apply (rule self_obseq_vars_untyped)
    by auto

definition "assign_default = foldl (\<lambda>p v. Seq p (Assign (pattern_1var v) 
                      (const_expression_untyped (vu_type v) (t_default (vu_type v))))) Skip"

lemma assign_default_welltyped: "well_typed (assign_default locals)"
  apply (induct locals rule:rev_induct)
  unfolding assign_default_def 
  using Rep_type eu_type_const_expression_untyped t_default_def t_domain_def by auto


definition "filter_global X = {x\<in>X. vu_global x}"
definition "filter_local X = {x\<in>X. \<not> vu_global x}"


lemma callproc_rule:
  fixes body pargs ret x args
    and V -- "variables that our observational equivalence talks about"
    and locals -- "(superset of) local variables of the procedure"
    and non_parg_locals -- "locals without variables from pargs"
  defines "p == Proc body pargs ret"
  (* defines "GL == {x. vu_global x}" *)
  assumes proc_locals: "filter_local (set(vars_untyped body) \<union> set(pu_vars pargs) \<union> set(eu_vars ret)) \<subseteq> set locals"
  assumes locals_local: "filter_global (set locals) = {}"
  assumes localsV: "V \<inter> set locals \<subseteq> set (pu_vars x)"
  assumes proc_globals: "filter_global (set(vars_untyped body) \<union> set(eu_vars ret)) \<subseteq> V"
  assumes argvarsV: "set(eu_vars args) \<subseteq> V"
  assumes non_parg_locals: "set non_parg_locals = set locals - set (pu_vars pargs)"
  defines "unfolded == Seq (Seq (Seq (Assign pargs args) (assign_default non_parg_locals)) body)
                           (Assign x ret)"
  shows "obs_eq_untyped V V (CallProc x p args) unfolded"
proof (unfold obs_eq_untyped_def rhoare_untyped_rhoare_denotation, rule rhoare_denotation_post_eq)
  define GL where "GL \<equiv> {x. vu_global x} :: variable_untyped set"
  have fl_GL: "\<And>X. filter_local X = X - GL"
    unfolding GL_def filter_local_def by auto
  have fg_GL: "\<And>X. filter_global X = X \<inter> GL"
    unfolding GL_def filter_global_def by auto
  have body_locals: "set(vars_untyped body) - GL \<subseteq> set locals" 
   and pargs_locals: "set(pu_vars pargs) - GL \<subseteq> set locals"
   and ret_locals: "set(eu_vars ret) - GL \<subseteq> set locals"
     using proc_locals unfolding fl_GL by auto
  have globalsVbody: "set(vars_untyped body) \<inter> GL \<subseteq> V"
   and globalsVret: "set(eu_vars ret) \<inter> GL \<subseteq> V"
     using proc_globals unfolding fg_GL by auto

  fix m1 m2 assume eq_init: "\<forall>x\<in>V. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"

  define eq where "eq \<equiv> \<lambda>V \<mu> \<nu>. apply_to_distr (\<lambda>m x. if x \<in> V then memory_lookup_untyped m x else undefined) \<mu>
                   = apply_to_distr (\<lambda>m x. if x \<in> V then memory_lookup_untyped m x else undefined) \<nu>" 

  define argvars where "argvars \<equiv> set (eu_vars args)"

  define untouched where "untouched \<equiv> \<lambda>V \<mu>. \<forall>m\<in>support_distr \<mu>. \<forall>x\<in>V. memory_lookup_untyped m x = memory_lookup_untyped m2 x"
  define G where "G \<equiv> {x\<in>V. vu_global x} :: variable_untyped set"
  define co_locals where "co_locals \<equiv> {x. \<not>vu_global x \<and> x\<notin>set locals}"

  define cp1 where "cp1 \<equiv> point_distr (memory_update_untyped_pattern (init_locals m1) pargs (eu_fun args m1))"
  define uf1 where "uf1 \<equiv> denotation_untyped (Seq (Assign pargs args) (assign_default non_parg_locals)) m2"

  define uf1_1 where "uf1_1 \<equiv> memory_update_untyped_pattern m2 pargs (eu_fun args m2)"
  define uf1_2 where "uf1_2 \<equiv> \<lambda>m2. foldl (\<lambda>m v. (\<lambda>m x. memory_update_untyped m x
               (eu_fun (const_expression_untyped (vu_type x) (t_default (vu_type x))) m)) m v) m2 non_parg_locals"
  have uf1: "uf1 = point_distr (uf1_2 uf1_1)"
  proof -
    have "denotation_untyped (Assign pargs args) m2 = point_distr uf1_1"
      by (simp add: memory_update_untyped_pattern_def uf1_1_def)
    hence l1: "uf1 = denotation_untyped (assign_default non_parg_locals) uf1_1"
      using uf1_def by fastforce
    have "denotation_untyped (assign_default non_parg_locals) uf1_1 = point_distr (uf1_2 uf1_1)"
      unfolding assign_default_def uf1_2_def
      apply (induct non_parg_locals rule: rev_induct)
      using Rep_type eu_fun_const_expression_untyped t_default_def t_domain_def by auto
    with l1 show "uf1 = point_distr (uf1_2 uf1_1)" by simp
  qed

  have eq1: "eq (G\<union>set locals) cp1 uf1"
  proof (unfold eq_def)
    define cp1mem where "cp1mem \<equiv> memory_update_untyped_pattern (init_locals m1) pargs (eu_fun args m1)"
    have cp1mem_uf: "\<forall>x\<in>(G\<union>set locals). memory_lookup_untyped cp1mem x = memory_lookup_untyped (uf1_2 (uf1_1)) x"
    proof
      fix x assume "x \<in> G \<union> set locals" 
      hence cases: "\<And>P. \<lbrakk> \<lbrakk> x \<notin> set (pu_vars pargs); x\<in>G \<rbrakk> \<Longrightarrow> P; 
                          \<lbrakk> x \<notin> set (pu_vars pargs); x\<in>set locals \<rbrakk> \<Longrightarrow> P; 
                          x \<in> set (pu_vars pargs) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"  by auto
      show "memory_lookup_untyped cp1mem x = memory_lookup_untyped (uf1_2 (uf1_1)) x"
      proof (rule cases)
        assume "x \<in> G" and not_pargs: "x \<notin> set (pu_vars pargs)"
        hence "x \<in> V" using G_def by auto
        from `x \<in> G` have "vu_global x" by (simp add: G_def)
        have init: "memory_lookup_untyped (init_locals m1) x = memory_lookup_untyped m1 x"
          unfolding Rep_init_locals by (simp add: `vu_global x`)
        have cp: "memory_lookup_untyped cp1mem x = memory_lookup_untyped m1 x" 
          unfolding cp1mem_def apply (subst memory_lookup_update_pattern_notsame)
          using not_pargs init .
        have uf_vg: "memory_lookup_untyped uf1_1 x == memory_lookup_untyped m2 x"
          unfolding uf1_1_def apply (subst memory_lookup_update_pattern_notsame)
          using not_pargs by blast
        have "x \<notin> set non_parg_locals"
          using `vu_global x` locals_local filter_global_def non_parg_locals by auto
        have uf: "memory_lookup_untyped (uf1_2 (uf1_1)) x = memory_lookup_untyped m2 x"
          unfolding uf1_2_def apply (insert `x \<notin> set non_parg_locals`)
          apply (induct non_parg_locals rule:rev_induct)
            close (auto simp: uf_vg)
          by (auto simp: memory_lookup_update_notsame_untyped)
        from cp uf eq_init `x\<in>V` show ?thesis by auto
      next
        assume "x \<in> set locals" and x_nin_pargs: "x \<notin> set (pu_vars pargs)"
        hence x_parg_non_locals: "x \<in> set non_parg_locals"
          by (simp add: non_parg_locals)
        have "\<not> vu_global x"
          using locals_local `x \<in> set locals` unfolding filter_global_def by auto
        have init: "memory_lookup_untyped (init_locals m1) x = t_default (vu_type x)"
          unfolding Rep_init_locals using `\<not> vu_global x` by auto
        have cp: "memory_lookup_untyped cp1mem x = t_default (vu_type x)"
          unfolding cp1mem_def 
          apply (subst memory_lookup_update_pattern_notsame) using x_nin_pargs init .
        have uf: "memory_lookup_untyped (uf1_2 uf1_1) x = t_default (vu_type x)"
          unfolding uf1_2_def apply (insert x_parg_non_locals, induct non_parg_locals rule:rev_induct)
          by (auto simp: eu_fun_const_expression_untyped memory_lookup_update_untyped)
        from cp uf show ?thesis by auto
      next
        assume xpargs: "x \<in> set (pu_vars pargs)"
        define vg where "vg \<equiv> pu_var_getters pargs"
        have vg: "\<exists>(v,g)\<in>set vg. v=x"
          using xpargs unfolding vg_def pu_vars_def by fastforce
        have "memory_lookup_untyped cp1mem x = memory_lookup_untyped (uf1_1) x"
          unfolding cp1mem_def memory_update_untyped_pattern_def uf1_1_def vg_def[symmetric]
          proof (insert vg, induction vg rule:rev_induct) 
          case Nil thus ?case by auto
          next case snoc show ?case apply auto
            by (smt Un_iff argvarsV case_prod_unfold empty_iff eq_init eu_fun_footprint insert_iff list.set(1) list.set(2) memory_lookup_update_untyped set_append snoc.IH snoc.prems subsetCE)
          qed
        moreover
        have x_nin_parg_locals: "x \<notin> set non_parg_locals"
          by (simp add: xpargs non_parg_locals)
        have "memory_lookup_untyped (uf1_1) x = memory_lookup_untyped (uf1_2 uf1_1) x"
          unfolding uf1_2_def apply (insert x_nin_parg_locals, induct non_parg_locals rule:rev_induct)
          using memory_lookup_update_untyped by auto
        finally show ?thesis.
      qed
    qed

    show "apply_to_distr (\<lambda>m x. if x \<in> G \<union> set locals then memory_lookup_untyped m x else undefined) (cp1) =
          apply_to_distr (\<lambda>m x. if x \<in> G \<union> set locals then memory_lookup_untyped m x else undefined) (uf1)"
      unfolding cp1_def cp1mem_def[symmetric] uf1 apply simp
      apply (rule cong[OF refl[of point_distr]])
      using cp1mem_uf by force
  qed

  have untouched1: "untouched co_locals uf1"
  proof (unfold uf1 untouched_def co_locals_def, auto)
    fix x assume "\<not> vu_global x" and "x \<notin> set locals"
    hence x_nin_pargs: "x \<notin> set (pu_vars pargs)" using pargs_locals GL_def by blast 
    have uf_vg: "memory_lookup_untyped uf1_1 x == memory_lookup_untyped m2 x"
      unfolding uf1_1_def apply (subst memory_lookup_update_pattern_notsame)
      by (simp_all add: x_nin_pargs)
    have "x \<notin> set non_parg_locals"
      using `x \<notin> set locals` non_parg_locals by auto
    show "memory_lookup_untyped (uf1_2 (uf1_1)) x = memory_lookup_untyped m2 x"
      unfolding uf1_2_def apply (insert `x \<notin> set non_parg_locals`)
      apply (induct non_parg_locals rule:rev_induct)
        close (auto simp: uf_vg)
      by (auto simp: memory_lookup_update_notsame_untyped)
  qed

  define uf2 where "uf2 \<equiv> compose_distr (denotation_untyped body) uf1"
  define cp2 where "cp2 \<equiv> compose_distr (denotation_untyped body) cp1"

  have eq_body: "obs_eq_untyped (G\<union>set locals) (G\<union>set locals) body body"
    apply (rule self_obseq_vars_untyped, rule, case_tac "x\<in>G", simp)
    apply auto using globalsVbody body_locals unfolding  GL_def G_def by auto

  have eq_compose': "\<And>P X Y \<mu> \<nu> f g. 
     eq X \<mu> \<nu> \<Longrightarrow> (\<forall>m\<in>support_distr \<nu>. P m) \<Longrightarrow> (\<exists>m. P m)
     \<Longrightarrow> rhoare_denotation (\<lambda>m1 m2. (\<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x) 
        \<and> P m2) f g
     (\<lambda>m1 m2. \<forall>x\<in>Y. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x) \<Longrightarrow>
     eq Y (compose_distr f \<mu>) (compose_distr g \<nu>)"
  proof -
    fix X Y \<mu> \<nu> f g P
    assume eq: "eq X \<mu> \<nu>"
    assume P: "\<forall>m\<in>support_distr \<nu>. P m"
    assume "\<exists>m. P m" then obtain m0 where "P m0" by auto
    assume eq2: "rhoare_denotation (\<lambda>m1 m2. (\<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x) \<and> P m2) f g
     (\<lambda>m1 m2. \<forall>x\<in>Y. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
    have rd1: "rhoare_denotation (\<lambda>m1' m2'. m1'=m0 \<and> m2'=m0)
          (\<lambda>m. if m=m0 then \<mu> else 0) (\<lambda>m. if m=m0 then \<nu> else 0)
          (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
      apply (rule rhoare_denotation_post_eq) using eq unfolding eq_def by auto
(*    have rd2: "rhoare_denotation (\<lambda>m1' m2'. m1'=m0 \<and> m2'=m0)
          (\<lambda>m. if m=m0 then \<mu> else 0) (\<lambda>m. if m=m0 then \<nu> else 0)
          (\<lambda>m1 m2. P m2)"
      unfolding rhoare_denotation_def apply auto
      apply (rule exI[of _ "product_distr \<mu> \<nu>"])
      apply auto
      by later *)
    have "rhoare_denotation (\<lambda>m1' m2'. m1'=m0 \<and> m2'=m0)
          (\<lambda>m. if m=m0 then \<mu> else 0) (\<lambda>m. if m=m0 then \<nu> else 0)
          (\<lambda>m1 m2. (\<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x) \<and> P m2)"
    proof -
      obtain \<mu>' where \<mu>: "apply_to_distr fst \<mu>' = \<mu>" and \<nu>: "apply_to_distr snd \<mu>' = \<nu>" 
        and post: "\<And>m1' m2'. (m1', m2') \<in> support_distr \<mu>' \<Longrightarrow> (\<forall>x\<in>X. memory_lookup_untyped m1' x = memory_lookup_untyped m2' x)"
        using rd1 unfolding rhoare_denotation_def by auto
      have P': "\<And>m1' m2'. (m1', m2') \<in> support_distr \<mu>' \<Longrightarrow> P m2'"
        using P \<nu> by fastforce
      show ?thesis
        unfolding rhoare_denotation_def apply simp apply (rule exI[of _ \<mu>'])
        using \<mu> \<nu> post P' by auto
    qed
    hence rhd: "rhoare_denotation (\<lambda>m1' m2'. m1'=m0 \<and> m2'=m0)
          (\<lambda>m. (compose_distr f ((\<lambda>m. if m=m0 then \<mu> else 0) m)))
          (\<lambda>m. (compose_distr g ((\<lambda>m. if m=m0 then \<nu> else 0) m)))
          (\<lambda>m1 m2. \<forall>x\<in>Y. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
      apply (rule rseq_rule_denotation)
      using eq2 unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation.
    show "eq Y (compose_distr f \<mu>) (compose_distr g \<nu>)"
      unfolding eq_def cp2_def uf2_def
      using rhoare_denotation_post_eq2[OF rhd] by simp
  qed

  have eq_compose: "\<And>X Y \<mu> \<nu> f g. 
     eq X \<mu> \<nu> \<Longrightarrow> rhoare_denotation (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x) f g
     (\<lambda>m1 m2. \<forall>x\<in>Y. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x) \<Longrightarrow>
     eq Y (compose_distr f \<mu>) (compose_distr g \<nu>)"
     by (rule_tac eq_compose', auto)
(*  proof -
    fix X Y \<mu> \<nu> f g
    assume eq: "eq X \<mu> \<nu>"
    assume eq2: "rhoare_denotation (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x) f g
     (\<lambda>m1 m2. \<forall>x\<in>Y. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
    have "rhoare_denotation (\<lambda>m1' m2'. m1'=m1 \<and> m2'=m2)
          (\<lambda>m. if m=m1 then \<mu> else 0) (\<lambda>m. if m=m2 then \<nu> else 0)
          (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
      apply (rule rhoare_denotation_post_eq) using eq unfolding eq_def by auto
    hence rhd: "rhoare_denotation (\<lambda>m1' m2'. m1'=m1 \<and> m2'=m2)
          (\<lambda>m. (compose_distr f ((\<lambda>m. if m=m1 then \<mu> else 0) m)))
          (\<lambda>m. (compose_distr g ((\<lambda>m. if m=m2 then \<nu> else 0) m)))
          (\<lambda>m1 m2. \<forall>x\<in>Y. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
      apply (rule rseq_rule_denotation)
      using eq2 unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation.
    show "eq Y (compose_distr f \<mu>) (compose_distr g \<nu>)"
      unfolding eq_def cp2_def uf2_def
      using rhoare_denotation_post_eq2[OF rhd] by simp
  qed *)

  have eq2: "eq (G\<union>set locals) cp2 uf2"
    unfolding cp2_def uf2_def apply (rule eq_compose)
    close (fact eq1) using eq_body unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation .

  have untouched2: "untouched co_locals uf2"
  proof (unfold untouched_def uf2_def, auto)
    fix m' m x
    assume "m' \<in> support_distr (uf1)" and x_co: "x \<in> co_locals"
    hence m'_m2: "memory_lookup_untyped m' x = memory_lookup_untyped m2 x"
      using untouched1 unfolding untouched_def by auto
    assume m: "m \<in> support_distr (denotation_untyped body m')"
    have "x \<notin> set(vars_untyped body)"
      using x_co body_locals unfolding GL_def co_locals_def by auto
    hence x: "x \<notin> set(write_vars_untyped body)" using write_vars_subset_vars_untyped by auto
    have m_m': "memory_lookup_untyped m x = memory_lookup_untyped m' x"
      apply (rule program_untyped_readonly_write_vars[where p=body, unfolded readonly_hoare_untyped hoare_untyped_def, rule_format])
      using m x by auto
    with m'_m2 show "memory_lookup_untyped m x = memory_lookup_untyped m2 x" by simp
  qed

  define uf3mem where "uf3mem \<equiv> \<lambda>m. memory_update_untyped_pattern m x (eu_fun ret m)"
  define uf3 where "uf3 \<equiv> compose_distr (denotation_untyped (Assign x ret)) uf2"
  define cp3mem where "cp3mem \<equiv> \<lambda>m'. let res = eu_fun ret m' in let m' = restore_locals m1 m' in
    memory_update_untyped_pattern m' x res"
  define cp3 where "cp3 \<equiv> apply_to_distr cp3mem cp2"
  
  have cp3: "cp3 = denotation_untyped (CallProc x p args) m1" 
    unfolding cp3_def cp3mem_def cp2_def p_def cp1_def by simp
  have uf3: "uf3 = denotation_untyped unfolded m2"
    unfolding uf3_def unfolded_def p_def uf2_def uf1_def by simp

  have uf3': "uf3 = apply_to_distr uf3mem uf2"
    unfolding uf3_def uf3mem_def denotation_untyped_Assign[THEN ext[of "denotation_untyped (Assign _ _)"]]
    by simp

  have eq3_almost: "\<And>m1' m2' y. 
            \<forall>x\<in>G \<union> set locals. memory_lookup_untyped m1' x = memory_lookup_untyped m2' x
        \<Longrightarrow> \<forall>x\<in>co_locals. memory_lookup_untyped m2' x = memory_lookup_untyped m2 x
        \<Longrightarrow> y \<in> V
        \<Longrightarrow> memory_lookup_untyped (cp3mem m1') y = memory_lookup_untyped (uf3mem m2') y"
  proof -
    fix m1' m2' y assume m'_eq: "\<forall>x\<in>G \<union> set locals. memory_lookup_untyped m1' x = memory_lookup_untyped m2' x"
    assume untouched: "\<forall>x\<in>co_locals. memory_lookup_untyped m2' x = memory_lookup_untyped m2 x"
    assume yV: "y \<in> V" (* ? cases:
      y \<in> set (pu_vars x) <- the return pattern:  then both sides get updated the same
      y \<in> non_parg_locals: should not happen (by y\<in>V) ?
      y \<in> co_locals: using "untouched2"
      y : globals - pu_vars x
    *)
    hence cases: "\<And>P. \<lbrakk> y \<in> set (pu_vars x) \<Longrightarrow> P; 
                        \<lbrakk> y \<in> co_locals; y\<notin>set(pu_vars x) \<rbrakk> \<Longrightarrow> P; 
                        \<lbrakk> vu_global y; y \<notin> set (pu_vars x) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
      apply atomize_elim unfolding co_locals_def G_def using localsV by auto
    show "memory_lookup_untyped (cp3mem m1') y = memory_lookup_untyped (uf3mem m2') y"
    proof (rule cases)
      assume y_pu_vars: "y \<in> set (pu_vars x)" 
      define vg where "vg \<equiv> pu_var_getters x"
      have vg: "\<exists>(v,g)\<in>set vg. v=y"
        using y_pu_vars unfolding vg_def pu_vars_def by fastforce
      have ret_locals': "\<And>x. \<lbrakk> x\<in>set(eu_vars ret); \<not> vu_global x \<rbrakk> \<Longrightarrow> x\<in>set locals" using ret_locals GL_def by auto
      have globalsVret': "\<And>x. x\<in>set(eu_vars ret) \<Longrightarrow> vu_global x \<Longrightarrow> x\<in>V" using globalsVret GL_def by auto
      show "memory_lookup_untyped (cp3mem m1') y = memory_lookup_untyped (uf3mem m2') y"
        unfolding cp3mem_def memory_update_untyped_pattern_def uf3mem_def vg_def[symmetric] apply simp
      proof (insert vg, induction vg rule:rev_induct) 
        case Nil thus ?case by auto
        next case snoc show ?case apply auto
          by (smt G_def Un_iff m'_eq case_prod_unfold empty_iff eu_fun_footprint globalsVret' insert_iff list.set(1) list.set(2)
              mem_Collect_eq memory_lookup_update_untyped ret_locals' set_append snoc.IH snoc.prems)
      qed
    next
      assume y_co_locals: "y \<in> co_locals" and y_nin_pu_vars: "y\<notin>set(pu_vars x)"
      hence y_local: "\<not> vu_global y" by (simp add: co_locals_def)
      have restore_locals: "memory_lookup_untyped (restore_locals m1 m1') y = memory_lookup_untyped m1 y"
        unfolding Rep_restore_locals by (simp add: y_local)
      have "memory_lookup_untyped (uf3mem m2') y = memory_lookup_untyped m2' y" 
        unfolding uf3mem_def apply (subst memory_lookup_update_pattern_notsame) using y_co_locals y_nin_pu_vars by auto
      also have "\<dots> = memory_lookup_untyped m2 y"
        using `y \<in> co_locals` untouched by auto
      also have "\<dots> = memory_lookup_untyped m1 y"
        using `y \<in> V` eq_init by auto
      also have "memory_lookup_untyped (cp3mem m1') y = memory_lookup_untyped m1 y"
        unfolding cp3mem_def apply (simp, subst memory_lookup_update_pattern_notsame) 
        using restore_locals y_nin_pu_vars by auto
      ultimately show ?thesis by simp
    next
      assume y_global: "vu_global y" and y_nin_pu_vars: "y \<notin> set (pu_vars x)"
      have restore_locals: "memory_lookup_untyped (restore_locals m1 m1') y = memory_lookup_untyped m1' y"
        unfolding Rep_restore_locals by (simp add: y_global)
      have "memory_lookup_untyped (uf3mem m2') y = memory_lookup_untyped m2' y" 
        unfolding uf3mem_def apply (subst memory_lookup_update_pattern_notsame) using y_nin_pu_vars by auto
      also have "\<dots> = memory_lookup_untyped m1' y"
        using G_def m'_eq yV y_global by force
      also have "\<dots> = memory_lookup_untyped (cp3mem m1') y"
        unfolding cp3mem_def apply simp apply (subst memory_lookup_update_pattern_notsame)
        using y_nin_pu_vars restore_locals by simp_all
      finally show ?thesis ..
    qed
  qed

  have eq3_almost': "\<And>m1' m2' y. (\<forall>x\<in>G \<union> set locals. memory_lookup_untyped m1' x = memory_lookup_untyped m2' x)
        \<and> (\<forall>x\<in>co_locals. memory_lookup_untyped m2' x = memory_lookup_untyped m2 x)
    \<Longrightarrow> 
              (\<lambda>x. if x \<in> V then memory_lookup_untyped (cp3mem m1') x else undefined) =
              (\<lambda>x. if x \<in> V then memory_lookup_untyped (uf3mem m2') x else undefined)"
    using eq3_almost by auto

  have eq3: "eq V cp3 uf3"
    unfolding uf3' cp3_def  compose_point_distr_l[symmetric]
    apply (rule eq_compose'[where P="\<lambda>m. \<forall>x\<in>co_locals. memory_lookup_untyped m x = memory_lookup_untyped m2 x"])
       close (fact eq2)
      using untouched2 close (auto simp: untouched_def)
     close (rule exI[of _ m2], simp)
    apply (rule rhoare_denotation_post_eq, simp)
    apply (subst eq3_almost') by auto

  from eq3 cp3 uf3
  show "apply_to_distr (\<lambda>m x. if x \<in> V then memory_lookup_untyped m x else undefined) (denotation_untyped (CallProc x p args) m1) =
        apply_to_distr (\<lambda>m x. if x \<in> V then memory_lookup_untyped m x else undefined) (denotation_untyped unfolded m2)" 
    unfolding eq_def by simp
qed


lemma hoare_obseq_replace_untyped:
  assumes Q: "assertion_footprint Y Q"
  assumes eq: "obs_eq_untyped X Y c d"
  assumes hoare: "hoare_untyped P d Q"
  shows "hoare_untyped P c Q"
proof (unfold hoare_untyped_def, rule+)
  fix m m' assume "P m" assume supp_m': "m' \<in> support_distr (denotation_untyped c m)"
  obtain \<mu> where supp: "\<And>m1 m2 x. (m1,m2)\<in>support_distr \<mu> \<Longrightarrow> x\<in>Y \<Longrightarrow> memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
        and fst: "apply_to_distr fst \<mu> = denotation_untyped c m" and snd: "apply_to_distr snd \<mu> = denotation_untyped d m"
    apply atomize_elim
    using eq[unfolded obs_eq_untyped_def rhoare_untyped_def, rule_format, of m m]
    by metis
  from supp_m' have "m' \<in> support_distr (apply_to_distr fst \<mu>)" using fst by simp
  then obtain m'd where m'd: "(m',m'd) \<in> support_distr \<mu>" by auto
  hence "m'd \<in> support_distr (apply_to_distr snd \<mu>)" by force
  hence "m'd \<in> support_distr (denotation_untyped d m)" using snd by auto
  hence "Q m'd" using hoare `P m` unfolding hoare_untyped_def by auto
  from m'd and supp have "\<And>x. x\<in>Y \<Longrightarrow> memory_lookup_untyped m' x = memory_lookup_untyped m'd x" by simp
  thus "Q m'"
    using Q `Q m'd` unfolding assertion_footprint_def by blast 
qed


lemma program_untyped_footprint_hoare:  
  assumes obseq: "obs_eq_untyped X X p p"
  assumes ro: "program_untyped_readonly (-X) p"
  shows "program_untyped_footprint X p"
unfolding program_untyped_footprint_def denotation_footprint_def apply auto
proof -
  fix m1 m1' z assume m1m1'_match: "memory_combine X default m1 = memory_combine X default m1'"
  define f where "f \<equiv> \<lambda>m. if (memory_combine X default m = memory_combine X default m1) 
                then memory_combine X m z
                else (if (memory_combine X default m = memory_combine X default z) then memory_combine X m m1 else m)"

  {fix m consider "memory_combine X default m = memory_combine X default m1" and
                  "memory_combine X default m = memory_combine X default z"
                | "memory_combine X default m \<noteq> memory_combine X default m1" and
                  "memory_combine X default m = memory_combine X default z"
                | "memory_combine X default m = memory_combine X default m1" and
                  "memory_combine X default m \<noteq> memory_combine X default z"
                | "memory_combine X default m \<noteq> memory_combine X default m1" and
                  "memory_combine X default m \<noteq> memory_combine X default z" by atomize_elim auto}
  then have ff: "f (f m) = m" for m
  proof (cases m)
  case 1
    have m1: "x \<notin> X \<Longrightarrow> memory_lookup_untyped m1 x = memory_lookup_untyped m x" for x
      using 1 unfolding Rep_memory_inject[symmetric] by (auto, metis)
    have z: "x \<notin> X \<Longrightarrow> memory_lookup_untyped z x = memory_lookup_untyped m x" for x
      using 1 unfolding Rep_memory_inject[symmetric] by (auto, metis)
    have "f m = memory_combine X m z"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      unfolding f_def using m1 by (simp_all add: 1)
    also have "memory_combine X m z = m"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      using z by simp_all
    finally show ?thesis by simp
  next case 2
    have z: "x \<notin> X \<Longrightarrow> memory_lookup_untyped z x = memory_lookup_untyped m x" for x
      using 2 unfolding Rep_memory_inject[symmetric] by (auto, metis)
    have m1z: "memory_combine X default z \<noteq> memory_combine X default m1"
      using 2 by simp
    have "f m = memory_combine X m m1"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      unfolding f_def by (auto simp: m1z 2)
    also have "f (memory_combine X m m1) = memory_combine X m z"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      unfolding f_def by (auto simp: m1z 2)
    also have "memory_combine X m z = m"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      unfolding f_def by (auto simp: z 2)
    finally show ?thesis by assumption
  next case 3
    have m1: "x \<notin> X \<Longrightarrow> memory_lookup_untyped m1 x = memory_lookup_untyped m x" for x
      using 3 unfolding Rep_memory_inject[symmetric] by (auto, metis)
    have m1z: "memory_combine X default z \<noteq> memory_combine X default m1"
      using 3 by simp
    have "f m = memory_combine X m z"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      unfolding f_def by (auto simp: 3)
    also have "f (memory_combine X m z) = memory_combine X m m1"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      unfolding f_def by (auto simp: m1z 3)
    also have "memory_combine X m m1 = m"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      using m1 by simp_all
    finally show ?thesis by simp
  next case 4
    have "f m = m"
      unfolding Rep_memory_inject[symmetric] 
      unfolding f_def by (simp add: 4)
    then show ?thesis by simp
  qed
  
  define m2 where "m2 == f m1"
  define eqX where "eqX == \<lambda>m1 m2. \<forall>x\<in>X. Rep_memory m1 x = Rep_memory m2 x"
  have "rhoare_untyped eqX p p eqX"
    using obseq unfolding obs_eq_untyped_def eqX_def by simp
  moreover have "eqX m1 m2"
    by (simp add: eqX_def f_def m2_def)
  ultimately obtain \<mu> where fst\<mu>: "apply_to_distr fst \<mu> = denotation_untyped p m1"
                      and snd\<mu>: "apply_to_distr snd \<mu> = denotation_untyped p m2"
                      and supp\<mu>: "\<And>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<Longrightarrow> eqX m1' m2'"
    unfolding rhoare_untyped_rhoare_denotation rhoare_denotation_def apply atomize_elim by auto
  have "\<forall>m1'\<in>support_distr (denotation_untyped p m1). memory_combine X default m1' = memory_combine X default m1"
    apply (subst Rep_memory_inject[symmetric])
    using ro unfolding program_untyped_readonly_def denotation_readonly_def by force
  then have supp\<mu>1: "\<And>m1' m2'. (m1',m2')\<in>support_distr \<mu> \<Longrightarrow>  memory_combine X default m1' = memory_combine X default m1"
    by (metis fst\<mu> fst_conv image_eqI support_apply_to_distr)
  have supp\<mu>2': "\<forall>m2'\<in>support_distr (denotation_untyped p m2). memory_combine X default m2' = memory_combine X default m2"
    apply (subst Rep_memory_inject[symmetric])
    using ro unfolding program_untyped_readonly_def denotation_readonly_def by force
  have supp\<mu>2: "(m1',m2')\<in>support_distr \<mu>
        \<Longrightarrow>  memory_combine X default m2' = memory_combine X default m2" for m1' m2'
  proof -
    assume "(m1',m2')\<in>support_distr \<mu>"
    hence "m2' \<in> support_distr (apply_to_distr snd \<mu>)"
      by force 
    hence "m2' \<in> support_distr (denotation_untyped p m2)" using snd\<mu> by auto
    thus ?thesis using supp\<mu>2' by fastforce
  qed
  have m2z: "memory_combine X default m2 = memory_combine X default z"
    unfolding m2_def f_def apply (subst Rep_memory_inject[symmetric])+ by auto
  have supp\<mu>_f: "(m1',m2')\<in>support_distr \<mu> \<Longrightarrow> m2' = f m1'" for m1' m2'
  proof -
    assume supp: "(m1',m2')\<in>support_distr \<mu>"
    have t1: "x\<in>X \<Longrightarrow> memory_lookup_untyped m1' x = memory_lookup_untyped m2' x" for x
      using supp\<mu> supp eqX_def by fastforce
    have "memory_combine X default m1' = memory_combine X default m1"
      using supp\<mu>1 supp by simp
    hence t2: "x\<notin>X \<Longrightarrow> Rep_memory m1' x = Rep_memory m1 x" for x
      unfolding Rep_memory_inject[symmetric] by (auto, metis)
    have "memory_combine X default m2' = memory_combine X default z"
      using supp\<mu>2 supp m2z by simp
    hence t3: "x\<notin>X \<Longrightarrow> Rep_memory m2' x = Rep_memory z x" for x
      unfolding Rep_memory_inject[symmetric] by (auto, metis)
    show ?thesis
      unfolding Rep_memory_inject[symmetric] f_def
      using t1 t2 t3 by (auto, metis)
  qed
  define \<mu>' where "\<mu>' == apply_to_distr (\<lambda>(m1',m2'). (m1',f m2')) \<mu>"
  have "\<And>m1' m2'. (m1',m2')\<in>support_distr \<mu>' \<Longrightarrow> m2' = m1'" 
    unfolding \<mu>'_def using supp\<mu>_f ff by auto 
  then have \<mu>'eq: "apply_to_distr fst \<mu>' = apply_to_distr snd \<mu>'"
    by (metis apply_to_distr_cong prod.collapse)
  
  have "denotation_untyped p m1 = apply_to_distr fst \<mu>"
    by (simp add: fst\<mu>)
  also have "\<dots> = apply_to_distr fst \<mu>'"
    unfolding \<mu>'_def apply simp
    apply (rewrite at "\<lambda>x. fst (case x of (m1',m2') \<Rightarrow> (m1',f m2'))" to fst   eq_reflection)
    by auto
  also have "\<dots> = apply_to_distr snd \<mu>'" 
    by (simp add: \<mu>'eq)
  also have "\<dots> = apply_to_distr f (apply_to_distr snd \<mu>)"
    unfolding \<mu>'_def apply simp
    apply (rewrite at "\<lambda>x. snd (case x of (m1',m2') \<Rightarrow> (m1',f m2'))" to "\<lambda>x. f (snd x)"  eq_reflection)
    by auto
  also have "\<dots> = apply_to_distr f (denotation_untyped p m2)"
    by (simp add: snd\<mu>)
  finally have "denotation_untyped p m1 = apply_to_distr f (denotation_untyped p m2)" by assumption
  
  then have "Rep_distr (denotation_untyped p m1) m1' = Rep_distr (apply_to_distr f (denotation_untyped p m2)) m1'" 
    unfolding Rep_distr_inject[symmetric] by simp
  also have "\<dots> = Rep_distr (denotation_untyped p m2) (f m1')"
    apply (rule Rep_apply_distr_biject) by (fact ff)+
  also have "m2 = memory_combine X m1 z"
    unfolding m2_def f_def apply (subst Rep_memory_inject[symmetric])+ by auto
  also have "f m1' = memory_combine X m1' z"
    unfolding f_def apply (subst Rep_memory_inject[symmetric])+ using m1m1'_match by auto
  finally show "Rep_distr (denotation_untyped p m1) m1' =
                Rep_distr (denotation_untyped p (memory_combine X m1 z)) (memory_combine X m1' z)" by assumption
next
  fix m m' assume "memory_combine X default m \<noteq> memory_combine X default m'"
  then show "Rep_distr (denotation_untyped p m) m' = 0" (* TODO remove ereal, change support_distr_def'' *)
    using ro unfolding program_untyped_readonly_def denotation_readonly_def support_distr_def'''
    apply (subst (asm) Rep_memory_inject[symmetric]) by fastforce
qed

lemma program_untyped_footprint_vars: "program_untyped_footprint (set(vars_untyped p)) p"
proof -
  have "obs_eq_untyped (set(vars_untyped p)) (set(vars_untyped p)) p p"
    by (simp add: self_obseq_vars_untyped)
  moreover have "program_untyped_readonly (- set(vars_untyped p)) p"
    by (meson Compl_anti_mono denotation_readonly_def program_untyped_readonly_def program_untyped_readonly_write_vars subsetCE write_vars_subset_vars_untyped(1))
  ultimately show ?thesis
    by (rule program_untyped_footprint_hoare)
qed


lemma frame_rule_untyped: 
  assumes foot1: "assertion_footprint_left X R" and foot2: "assertion_footprint_right Y R"
  assumes ro1: "program_untyped_readonly X p1" and ro2: "program_untyped_readonly Y p2"
  assumes rhoare: "rhoare_untyped P p1 p2 Q"
  shows "rhoare_untyped (\<lambda>m1 m2. P m1 m2 \<and> R m1 m2) p1 p2 (\<lambda>m1 m2. Q m1 m2 \<and> R m1 m2)"
proof (rule rhoare_untypedI, goal_cases)
case (1 m1 m2) 
  hence P: "P m1 m2" and R: "R m1 m2" by simp_all
  then obtain \<mu> where fst: "apply_to_distr fst \<mu> = denotation_untyped p1 m1"
                and snd: "apply_to_distr snd \<mu> = denotation_untyped p2 m2" 
                and supp: "\<And>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<Longrightarrow> Q m1' m2'"
    apply atomize_elim by (rule rhoare[THEN rhoare_untypedE])
  have QR: "Q m1' m2' \<and> R m1' m2'" if m1m2': "(m1',m2') \<in> support_distr \<mu>" for m1' m2'
  proof -
    from m1m2' have "m1' \<in> support_distr (denotation_untyped p1 m1)"
      unfolding fst[symmetric] by (simp add: rev_image_eqI) 
    hence m1_ro: "\<And>x. x\<in>X \<Longrightarrow> Rep_memory m1 x = Rep_memory m1' x"
      using ro1 unfolding program_untyped_readonly_def denotation_readonly_def by auto
    from m1m2' have "m2' \<in> support_distr (denotation_untyped p2 m2)"
      unfolding snd[symmetric] by (simp add: rev_image_eqI) 
    hence m2_ro: "\<And>x. x\<in>Y \<Longrightarrow> Rep_memory m2 x = Rep_memory m2' x"
      using ro2 unfolding program_untyped_readonly_def denotation_readonly_def by auto
    from m1_ro and m2_ro have "R m1' m2'"
      using R foot1 foot2 unfolding assertion_footprint_left_def assertion_footprint_right_def
      apply auto by blast
    thus ?thesis
      by (simp add: supp m1m2')
  qed

  show ?case
    apply (rule exI[of _ \<mu>]) using fst snd QR by simp
qed


(*
TODO: (https://www.easycrypt.info/trac/raw-attachment/wiki/BibTex/Barthe.2009.POPL.pdf)
- rand (one sided)
- while
- if
- case (+ hoare)
*)

end