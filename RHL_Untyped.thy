theory RHL_Untyped
imports Lang_Untyped Hoare_Untyped "~~/src/HOL/Library/Rewrite"
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
  def witness == "product_distr (denotation_untyped c m1) (denotation_untyped Skip m2)"
  show " \<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped c m1 \<and>
             apply_to_distr snd \<mu> = denotation_untyped Skip m2 \<and>
             (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2')"
    apply (rule exI[where x=witness])
    unfolding witness_def apply auto
    apply (metis scaleR_one_distr)
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
  def witness' == "apply_to_distr (\<lambda>(x,y). (y,x)) witness"
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
  def map == "\<lambda>(xval,yval). (memory_update_untyped_pattern m1 x xval, memory_update_untyped_pattern m2 y yval)"
  def \<mu>' == "apply_to_distr map (\<mu> m1 m2)"
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

(* TODO remove 
lemma rnd_rule:
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow> apply_to_distr fst (\<mu> m1 m2) = ed_fun d m1"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> apply_to_distr snd (\<mu> m1 m2) = ed_fun e m2"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>(xval,yval)\<in>support_distr (\<mu> m1 m2). 
           Q (memory_update_untyped m1 x xval) (memory_update_untyped m2 y yval)"
  shows "rhoare_untyped P (Sample x d) (Sample y e) Q"
  unfolding rhoare_untyped_def apply rule+ defer apply rule
proof -
  fix m1 m2 assume "P m1 m2"
  def map == "\<lambda>(xval,yval). (memory_update_untyped m1 x xval, memory_update_untyped m2 y yval)"
  def \<mu>' == "apply_to_distr map (\<mu> m1 m2)"
  have mu1: "apply_to_distr fst (\<mu> m1 m2) = ed_fun d m1" using assms `P m1 m2` by simp
  have mu2: "apply_to_distr snd (\<mu> m1 m2) = ed_fun e m2" using assms `P m1 m2` by simp
  have post: "\<forall>(xval,yval)\<in>support_distr (\<mu> m1 m2). Q (memory_update_untyped m1 x xval) (memory_update_untyped m2 y yval)"
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
*)

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
  def \<mu> == "apply_to_distr (\<lambda>(x,y,z). (x,z)) \<mu>3"
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
  def \<mu>' == "\<lambda>(m1,m2). \<mu>0 m1 m2"
  def \<mu>'' == "compose_distr \<mu>' \<mu>"
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
  def \<mu>' == "\<lambda>(m1,m2). \<mu>0 m1 m2"
  def \<mu>'' == "compose_distr \<mu>' \<mu>"
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
SORRY

lemma rhoare_denotation_post_eq2: 
  fixes X c1 c2 P
  defines "project == (\<lambda>m x. if x\<in>X then memory_lookup_untyped m x else undefined)"
  assumes "rhoare_denotation P c1 c2 (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
  shows "\<And>m1 m2. P m1 m2 \<Longrightarrow> apply_to_distr project (c1 m1) = apply_to_distr project (c2 m2)"
SORRY

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
SORRY


lemma self_obseq_vars:
  assumes "set(vars_untyped c) \<subseteq> X"
  assumes "Y \<subseteq> X"
  shows "obs_eq_untyped X Y c c"
SORRY

lemma self_obseq_assign:
  assumes "set (eu_vars e) \<subseteq> X"
  assumes "Y \<subseteq> X\<union>set(p_vars pat)"
  shows "obs_eq_untyped X Y (Assign pat e) (Assign pat e)"
SORRY

(*
fun assign_local_vars :: "variable_untyped list \<Rightarrow> variable_untyped list \<Rightarrow> expression_untyped list \<Rightarrow> program_rep" where
  "assign_local_vars [] [] [] = Skip"
| "assign_local_vars locals (v#vs) (e#es) = Seq (assign_local_vars locals vs es) (Assign (pattern_1var v) e)"
| "assign_local_vars (x#locals) [] [] = Seq (assign_local_vars locals [] [])
        (Assign (pattern_1var x) (const_expression_untyped (vu_type x) (t_default (vu_type x))))"
| "assign_local_vars locals [] (e#es) = assign_local_vars locals [] []"
| "assign_local_vars locals (v#vs) [] = assign_local_vars locals [] []"
*)

(*
definition "assign_local_vars (locals::variable_untyped list) vs es = 
  fold (\<lambda>(x,e) p. Seq p (Assign x e)) (zip vs es)
  (fold (\<lambda>x p. Seq p (Assign x (const_expression_untyped (vu_type x) (t_default (vu_type x))))) 
  locals Skip)"
*)

(*
lemma well_typed_assign_local_vars:
  assumes "map vu_type vs = map eu_type es"
  shows "well_typed (assign_local_vars locals vs es)"
proof -
  have wt_nil: "well_typed (assign_local_vars locals [] [])"
    apply (induction locals)
    by (auto simp: eu_type_const_expression_untyped)
  have vs_es_type: "\<forall>(v,e)\<in>set (zip vs es). eu_type e = vu_type v"
    using assms[unfolded list_eq_iff_zip_eq] unfolding zip_map_map by auto
  show "well_typed (assign_local_vars locals vs es)"
    apply (insert vs_es_type)
    apply (induction vs es rule:list_induct2') 
    using wt_nil by auto
qed
*)

lemma foldr_commute:  (* TODO used? *)
  assumes "\<And>x y. f (g x y) = g' x (f y)"
  shows "f (foldr g l a) = foldr g' l (f a)"
    apply (induction l)
    using assms by auto

lemma foldl_commute: 
  assumes "\<And>x y. f (g x y) = g' (f x) y"
  shows "f (foldl g a l) = foldl g' (f a) l"
    apply (induction l rule:rev_induct)
    using assms by auto

lemma foldr_o:  (* TODO used? *)
  shows "(foldr (\<lambda>x. op o (f x)) l a) m = foldr f l (a m)"
  by (induction l, auto)

(* TODO need? *)
lemma zip_hd: 
  assumes "(a, b) # x = zip as bs"
  shows "as = a#tl as" and "bs = b#tl bs"
apply (insert assms)
apply (induction bs, auto)
apply (metis list.exhaust list.sel(1) list.sel(3) prod.sel(1) zip_Cons_Cons zip_Nil)
apply (induction bs arbitrary: as, auto)
by (metis Pair_inject list.distinct(2) list.exhaust list.inject zip_Cons_Cons zip_Nil)

definition "assign_default = foldl (\<lambda>p v. Seq p (Assign (pattern_1var v) 
                      (const_expression_untyped (vu_type v) (t_default (vu_type v))))) Skip"

lemma assign_default_welltyped: "well_typed (assign_default locals)"
  apply (induct locals rule:rev_induct)
  unfolding assign_default_def 
  using Rep_type eu_type_const_expression_untyped t_default_def t_domain_def by auto

(* TODO move *)
lemma memory_lookup_update_pattern_notsame:
  assumes "x \<notin> set (pu_vars p)"
  shows "memory_lookup_untyped (memory_update_untyped_pattern m p a) x = memory_lookup_untyped m x"
proof -
  def vg == "pu_var_getters p"
  hence vg: "x \<notin> fst ` set vg"
    using assms pu_var_getters_def pu_vars_def by auto
  show ?thesis
    unfolding memory_update_untyped_pattern_def  vg_def[symmetric]
    apply (insert vg)
    apply (induct vg rule:rev_induct)
     by (auto simp: memory_lookup_update_notsame_untyped)
qed


lemma callproc_rule:
  fixes body pargs ret x args
    and V -- "variables that our observational equivalence talks about"
    and locals -- "(superset of) local variables of the procedure"
    and non_parg_locals -- "locals without variables from pargs"
  defines "p == Proc body pargs ret"
  defines "GL == {x. vu_global x}"
  assumes proc_locals: "(set(vars_untyped body) \<union> set(pu_vars pargs) \<union> set(eu_vars ret)) - GL \<subseteq> set locals"
  assumes locals_local: "GL \<inter> set locals = {}"
  assumes localsV: "V \<inter> set locals \<subseteq> set (pu_vars x)"
  assumes proc_globals: "(set(vars_untyped body) \<union> set(eu_vars ret)) \<inter> GL \<subseteq> V"
  assumes argvarsV: "set(eu_vars args) \<subseteq> V"
  assumes non_parg_locals: "set non_parg_locals = set locals - set (pu_vars pargs)"
  defines "unfolded == Seq (Seq (Seq (Assign pargs args) (assign_default non_parg_locals)) body)
                           (Assign x ret)"
  shows "obs_eq_untyped V V (CallProc x p args) unfolded"
proof (unfold obs_eq_untyped_def rhoare_untyped_rhoare_denotation, rule rhoare_denotation_post_eq)
  have body_locals: "set(vars_untyped body) - GL \<subseteq> set locals" 
   and pargs_locals: "set(pu_vars pargs) - GL \<subseteq> set locals"
   and ret_locals: "set(eu_vars ret) - GL \<subseteq> set locals"
     using proc_locals by auto
  have globalsVbody: "set(vars_untyped body) \<inter> GL \<subseteq> V"
   and globalsVret: "set(eu_vars ret) \<inter> GL \<subseteq> V"
     using proc_globals by auto

  fix m1 m2 assume eq_init: "\<forall>x\<in>V. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"

  def eq == "\<lambda>V \<mu> \<nu>. apply_to_distr (\<lambda>m x. if x \<in> V then memory_lookup_untyped m x else undefined) \<mu>
                   = apply_to_distr (\<lambda>m x. if x \<in> V then memory_lookup_untyped m x else undefined) \<nu>" 
(*  have "eq = (\<lambda>V \<mu> \<nu>. apply_to_distr (\<lambda>m x. if x \<in> V then memory_lookup_untyped m x else undefined) \<mu>
                   = apply_to_distr (\<lambda>m x. if x \<in> V then memory_lookup_untyped m x else undefined) \<nu>)" *)
(*  def eq == "\<lambda>X c1 c2. rhoare_denotation (\<lambda>m1 m2. \<forall>x\<in>V. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)
                                         c1 c2
                                         (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)" 
  have eq_mono: "\<And>A B c1 c2. A \<subseteq> B \<Longrightarrow> eq B c1 c2 \<Longrightarrow> eq A c1 c2" 
    unfolding eq_def rhoare_denotation_def by blast *)

  def argvars == "set (eu_vars args)"

  def untouched == "\<lambda>V \<mu>. \<forall>m\<in>support_distr \<mu>. \<forall>x\<in>V. memory_lookup_untyped m x = memory_lookup_untyped m2 x"
  def G == "{x\<in>V. vu_global x} :: variable_untyped set"
  def co_locals == "{x. \<not>vu_global x \<and> x\<notin>set locals}"

  def cp1 == "point_distr (memory_update_untyped_pattern (init_locals m1) pargs (eu_fun args m1))"
  def uf1 == "denotation_untyped (Seq (Assign pargs args) (assign_default non_parg_locals)) m2"

(*  def uf1_1 == "foldl (\<lambda>m (v, f). memory_update_untyped m v (f (eu_fun args m2))) m2 (pu_var_getters pargs)" *)
  def uf1_1 == "memory_update_untyped_pattern m2 pargs (eu_fun args m2)"
  def uf1_2 == "\<lambda>m2. foldl (\<lambda>m v. (\<lambda>m x. memory_update_untyped m x
               (eu_fun (const_expression_untyped (vu_type x) (t_default (vu_type x))) m)) m v) m2 non_parg_locals"
  have uf1: "uf1 = point_distr (uf1_2 uf1_1)"
  proof -
    have "denotation_untyped (Assign pargs args) m2 = point_distr uf1_1"
      by (simp add: memory_update_untyped_pattern_def uf1_1_def)
    hence l1: "uf1 = denotation_untyped (assign_default non_parg_locals) uf1_1"
      using uf1_def by fastforce
    have "denotation_untyped (assign_default non_parg_locals) uf1_1 = point_distr (uf1_2 uf1_1)"
      unfolding assign_default_def uf1_2_def
      apply (induct non_parg_locals rule: rev_induct) by auto
    with l1 show "uf1 = point_distr (uf1_2 uf1_1)" by simp
  qed

  have eq1: "eq (G\<union>set locals) cp1 uf1"
  proof (unfold eq_def)
(*  proof (unfold eq_def, rule rhoare_denotation_post_eq) *)
(*    assume init_eqV: "\<forall>x\<in>V. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x" *)
    def cp1mem == "memory_update_untyped_pattern (init_locals m1) pargs (eu_fun args m1)"
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
          unfolding init_locals_def memory_lookup_untyped_def apply (simp add: `vu_global x`)
          apply (subst Abs_memory_inverse) using Rep_memory by auto
        have cp: "memory_lookup_untyped cp1mem x = memory_lookup_untyped m1 x" 
          unfolding cp1mem_def apply (subst memory_lookup_update_pattern_notsame)
          using not_pargs init .
        have uf_vg: "memory_lookup_untyped uf1_1 x == memory_lookup_untyped m2 x"
          unfolding uf1_1_def apply (subst memory_lookup_update_pattern_notsame)
          using not_pargs by blast
        have "x \<notin> set non_parg_locals"
          using `vu_global x` locals_local GL_def non_parg_locals by auto
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
          using locals_local `x \<in> set locals` unfolding GL_def by auto
        have init: "memory_lookup_untyped (init_locals m1) x = t_default (vu_type x)"
          unfolding init_locals_def memory_lookup_untyped_def using `\<not> vu_global x` apply auto
          apply (subst Abs_memory_inverse) using Rep_memory by auto
        have cp: "memory_lookup_untyped cp1mem x = t_default (vu_type x)"
          unfolding cp1mem_def 
          apply (subst memory_lookup_update_pattern_notsame) using x_nin_pargs init .
        have uf: "memory_lookup_untyped (uf1_2 uf1_1) x = t_default (vu_type x)"
          unfolding uf1_2_def apply (insert x_parg_non_locals, induct non_parg_locals rule:rev_induct)
          by (auto simp: eu_fun_const_expression_untyped memory_lookup_update_untyped)
        from cp uf show ?thesis by auto
      next
        assume xpargs: "x \<in> set (pu_vars pargs)"
        def vg == "pu_var_getters pargs"
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

  def uf2 == "compose_distr (denotation_untyped body) uf1"
  def cp2 == "compose_distr (denotation_untyped body) cp1"

  have eq_body: "obs_eq_untyped (G\<union>set locals) (G\<union>set locals) body body"
    apply (rule self_obseq_vars, rule, case_tac "x\<in>G", simp)
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
    have x: "x \<notin> set(vars_untyped body)"
      using x_co body_locals unfolding GL_def co_locals_def by auto
    have m_m': "memory_lookup_untyped m x = memory_lookup_untyped m' x"
      apply (rule readonly_notin_vars[unfolded hoare_untyped_def, rule_format, where c=body and m=m'])
      using m x by auto
    with m'_m2 show "memory_lookup_untyped m x = memory_lookup_untyped m2 x" by simp
  qed

  def uf3mem == "\<lambda>m. memory_update_untyped_pattern m x (eu_fun ret m)"
  def uf3 == "compose_distr (denotation_untyped (Assign x ret)) uf2"
  def cp3mem == "\<lambda>m'. let res = eu_fun ret m' in let m' = restore_locals m1 m' in
    memory_update_untyped_pattern m' x res"
  def cp3 == "apply_to_distr cp3mem cp2"
  
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
      def vg == "pu_var_getters x"
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
        unfolding restore_locals_def memory_lookup_untyped_def apply (simp add: y_local)
        apply (subst Abs_memory_inverse) using Rep_memory by auto
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
        unfolding restore_locals_def memory_lookup_untyped_def apply (simp add: y_global)
        apply (subst Abs_memory_inverse) using Rep_memory by auto
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




(*
lemma rseq_rule1:
  assumes "\<And>m1 m2. Q m1 m2 \<Longrightarrow> Q' m1 m2"
      and "rhoare_untyped P c1 Skip Q"
      and "rhoare_untyped Q' Skip c2 R"
  shows "rhoare_untyped P c1 c2 R"
SORRY


lemma rif_rule:
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow> eu_fun e1 m1 = eu_fun e2 m2"
      and "rhoare_untyped (\<lambda>m1 m2. P m1 m2 \<and> eu_fun e1 m1 = embedding True) then1 then2 Q"
      and "rhoare_untyped (\<lambda>m1 m2. P m1 m2 \<and> eu_fun e1 m1 \<noteq> embedding True) else1 else2 Q"
  shows "rhoare_untyped P (IfTE e1 then1 else1) (IfTE e2 then2 else2) Q"
SORRY
*)

(*
TODO: (https://www.easycrypt.info/trac/raw-attachment/wiki/BibTex/Barthe.2009.POPL.pdf)
- rand (one sided)
- while
- if
- case (+ hoare)
*)

end