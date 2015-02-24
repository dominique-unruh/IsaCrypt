theory RHL_Untyped
imports Lang_Untyped Hoare_Untyped
begin

definition rhoare :: "(memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> program \<Rightarrow> (memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "rhoare pre c1 c2 post =
  (\<forall>m1 m2. pre m1 m2 \<longrightarrow> 
     (\<exists>\<mu>. apply_to_ell1 fst \<mu> = denotation c1 m1
        \<and> apply_to_ell1 snd \<mu> = denotation c2 m2
        \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_ell1 \<mu> \<longrightarrow> post m1' m2')))";

lemma rskip_rule:
  assumes "\<forall>m1 m2. P m1 m2 \<longrightarrow> Q m1 m2"
  shows "rhoare P Skip Skip Q"
  sorry

lemma rconseq_rule:
  assumes "\<forall>m1 m2. P m1 m2 \<longrightarrow> P' m1 m2"
      and "\<forall>m1 m2. Q' m1 m2 \<longrightarrow> Q m1 m2"
      and "rhoare P' c1 c2 Q'"
  shows "rhoare P c1 c2 Q"
  using assms unfolding rhoare_def by metis

lemma hoare_to_rhoare:
  assumes "lossless c"
      and h:"\<forall>m2. hoare (\<lambda>m1. P m1 m2) c (\<lambda>m1. Q m1 m2)"
  shows "rhoare P c Skip Q"
proof (unfold rhoare_def, rule, rule, rule)
  fix m1 m2 assume Pm1m2: "P m1 m2"
  def witness == "product_ell1 (denotation c m1) (denotation Skip m2)"
  show " \<exists>\<mu>. apply_to_ell1 fst \<mu> = denotation c m1 \<and>
             apply_to_ell1 snd \<mu> = denotation Skip m2 \<and>
             (\<forall>m1' m2'. (m1', m2') \<in> support_ell1 \<mu> \<longrightarrow> Q m1' m2')"
    apply (rule exI[where x=witness])
    unfolding witness_def apply auto
    using assms apply (metis lossless_def scaleR_one)
    by (metis Pm1m2 h hoare_def)
qed
  
lemma rsymmetric_rule:
  assumes "rhoare (\<lambda>m1 m2. P m2 m1) c2 c1 (\<lambda>m1 m2. Q m2 m1)"
  shows "rhoare P c1 c2 Q"
proof (unfold rhoare_def, rule, rule, rule)
  fix m1 m2 assume P: "P m1 m2"
  obtain witness where wit2: "apply_to_ell1 fst witness = denotation c2 m2"
                   and wit1: "apply_to_ell1 snd witness = denotation c1 m1"
                   and correct: "\<forall>m1' m2'. (m1', m2') \<in> support_ell1 witness \<longrightarrow> Q m2' m1'"
       by (metis (mono_tags) P assms rhoare_def)
  def witness' == "apply_to_ell1 (\<lambda>(x,y). (y,x)) witness"
  have wit'1: "apply_to_ell1 fst witness' = denotation c1 m1"
    unfolding witness'_def wit1[symmetric] apply auto
    apply (rule cong[where x=witness], rule cong[where f=apply_to_ell1])
    by auto
  have wit'2: "apply_to_ell1 snd witness' = denotation c2 m2"
    unfolding witness'_def wit2[symmetric] apply auto
    apply (rule cong[where x=witness], rule cong[where f=apply_to_ell1])
    by auto
  also have correct': "\<forall>m1 m2. (m1, m2) \<in> support_ell1 witness' \<longrightarrow> Q m1 m2"
    unfolding witness'_def using correct by auto

  show "\<exists>\<mu>. apply_to_ell1 fst \<mu> = denotation c1 m1 \<and>
                  apply_to_ell1 snd \<mu> = denotation c2 m2 \<and> (\<forall>m1' m2'. (m1', m2') \<in> support_ell1 \<mu> \<longrightarrow> Q m1' m2')"
    using wit'1 wit'2 correct' by auto            
qed

lemma rassign_rule1:
  assumes "\<forall>m1 m2. P m1 m2 \<longrightarrow> Q (memory_update_untyped m1 x (eu_fun e m1)) m2"
  shows "rhoare P (Assign x e) Skip Q"
  apply (rule hoare_to_rhoare)
  unfolding lossless_def apply simp
  apply (rule allI, rule assign_rule)
  using assms by simp

lemma rassign_rule2:
  assumes "\<forall>m1 m2. P m1 m2 \<longrightarrow> Q m1 (memory_update_untyped m2 x (eu_fun e m2))"
  shows "rhoare P Skip (Assign x e) Q"
apply (rule rsymmetric_rule)
apply (rule rassign_rule1)
using assms by simp

(*
TODO: (https://www.easycrypt.info/trac/raw-attachment/wiki/BibTex/Barthe.2009.POPL.pdf)
- rand (+ hoare)
- cond
- while
- trans
- case (+ hoare)

Is there a rule like:
 \<forall>m2. {Q &m m2} c {P &m m2} \<Longrightarrow> {Q} c ~ skip {P} ?
*)

end