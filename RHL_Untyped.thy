theory RHL_Untyped
imports Lang_Untyped Hoare_Untyped
begin

definition rhoare_untyped :: "(memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> program_rep \<Rightarrow> program_rep \<Rightarrow> (memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "rhoare_untyped pre c1 c2 post =
  (\<forall>m1 m2. pre m1 m2 \<longrightarrow> 
     (\<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped c1 m1
        \<and> apply_to_distr snd \<mu> = denotation_untyped c2 m2
        \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> post m1' m2')))";

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
  assumes "\<forall>m1 m2. P m1 m2 \<longrightarrow> Q (memory_update_untyped m1 x (eu_fun e m1)) m2"
  shows "rhoare_untyped P (Assign x e) Skip Q"
  apply (rule hoare_to_rhoare)
  unfolding lossless_untyped_def apply simp
  apply (rule allI, rule assign_rule)
  using assms by simp

lemma rassign_rule2:
  assumes "\<forall>m1 m2. P m1 m2 \<longrightarrow> Q m1 (memory_update_untyped m2 x (eu_fun e m2))"
  shows "rhoare_untyped P Skip (Assign x e) Q"
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
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>(xval,yval)\<in>support_distr (\<mu> m1 m2). Q (memory_update_untyped m1 x xval) (memory_update_untyped m2 y yval)"
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
              and \<mu>1supp: "\<And>m1' m'. (m1',m') \<in> support_distr \<mu>1 \<Longrightarrow> Q1 m1' m'";
    using `P1 m1 m` rhl1 unfolding rhoare_untyped_def by metis
  obtain \<mu>2 where \<mu>2fst: "apply_to_distr fst \<mu>2 = denotation_untyped c m"
              and \<mu>2snd: "apply_to_distr snd \<mu>2 = denotation_untyped c2 m2"
              and \<mu>2supp: "\<And>m' m2'. (m',m2') \<in> support_distr \<mu>2 \<Longrightarrow> Q2 m' m2'";
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

(*
lemma rseq_rule1:
  assumes "\<And>m1 m2. Q m1 m2 \<Longrightarrow> Q' m1 m2"
      and "rhoare_untyped P c1 Skip Q"
      and "rhoare_untyped Q' Skip c2 R"
  shows "rhoare_untyped P c1 c2 R"
sorry


lemma rif_rule:
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow> eu_fun e1 m1 = eu_fun e2 m2"
      and "rhoare_untyped (\<lambda>m1 m2. P m1 m2 \<and> eu_fun e1 m1 = embedding True) then1 then2 Q"
      and "rhoare_untyped (\<lambda>m1 m2. P m1 m2 \<and> eu_fun e1 m1 \<noteq> embedding True) else1 else2 Q"
  shows "rhoare_untyped P (IfTE e1 then1 else1) (IfTE e2 then2 else2) Q"
sorry
*)

(*
TODO: (https://www.easycrypt.info/trac/raw-attachment/wiki/BibTex/Barthe.2009.POPL.pdf)
- rand (one sided)
- while
- if
- case (+ hoare)
*)

end