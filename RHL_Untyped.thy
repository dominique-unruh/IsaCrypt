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
  unfolding rhoare_def apply (rule, rule, rule)
  apply (rule_tac x="point_ell1 (m1,m2)" in exI)
  using assms by simp

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
lemma rnd_rule:
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>y\<in>support_distr (ed_fun e m2). y = f (f' y)"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>x\<in>support_distr (ed_fun d m1). x = f' (f x)"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>y\<in>support_distr (ed_fun e m2). prob (ed_fun e m2) y = prob (ed_fun d m1) (f' y)"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>x\<in>support_distr (ed_fun d m1). f x \<in> support_distr (ed_fun e m2)"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>x\<in>support_distr (ed_fun d m1). Q (memory_update_untyped m1 x) (memory_update_untyped m2 (f x))"
  shows "rhoare P (Sample x d) (Sample y e) Q"
*)

lemma rnd_rule:
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow> apply_to_distr fst (\<mu> m1 m2) = ed_fun d m1"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> apply_to_distr snd (\<mu> m1 m2) = ed_fun e m2"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>(xval,yval)\<in>support_distr (\<mu> m1 m2). Q (memory_update_untyped m1 x xval) (memory_update_untyped m2 y yval)"
  shows "rhoare P (Sample x d) (Sample y e) Q"
  unfolding rhoare_def apply rule+ defer apply rule
proof -
  fix m1 m2 assume "P m1 m2"
  def map == "\<lambda>(xval,yval). (memory_update_untyped m1 x xval, memory_update_untyped m2 y yval)"
  def \<mu>' == "apply_to_ell1 map (distr_to_ell1 (\<mu> m1 m2))"
  have mu1: "apply_to_distr fst (\<mu> m1 m2) = ed_fun d m1" using assms `P m1 m2` by simp
  have mu2: "apply_to_distr snd (\<mu> m1 m2) = ed_fun e m2" using assms `P m1 m2` by simp
  have post: "\<forall>(xval,yval)\<in>support_distr (\<mu> m1 m2). Q (memory_update_untyped m1 x xval) (memory_update_untyped m2 y yval)"
    using assms `P m1 m2` by simp
  show "apply_to_ell1 fst \<mu>' = denotation (Sample x d) m1"
    unfolding \<mu>'_def apply simp
    unfolding mu1[symmetric] apply simp
    apply (rule cong[where x="distr_to_ell1 (\<mu> m1 m2)"])
    apply (rule cong[where f="apply_to_ell1"], simp)
    unfolding map_def by auto
  show "apply_to_ell1 snd \<mu>' = denotation (Sample y e) m2" 
    unfolding \<mu>'_def apply simp
    unfolding mu2[symmetric] apply simp
    apply (rule cong[where x="distr_to_ell1 (\<mu> m1 m2)"])
    apply (rule cong[where f="apply_to_ell1"], simp)
    unfolding map_def by auto
  show "\<forall>m1' m2'. (m1', m2') \<in> support_ell1 \<mu>' \<longrightarrow> Q m1' m2'" 
    unfolding \<mu>'_def map_def using post by auto
qed

lemma rtrans_rule:
  assumes p:"\<And>m1 m2. P m1 m2 \<Longrightarrow> \<exists>m. P1 m1 m \<and> P2 m m2"
      and q:"\<And>m1 m2 m. Q1 m1 m \<Longrightarrow> Q2 m m2 \<Longrightarrow> Q m1 m2"
      and rhl1: "rhoare P1 c1 c Q1"
      and rhl2: "rhoare P2 c c2 Q2"
  shows "rhoare P c1 c2 Q"
proof (unfold rhoare_def, auto, rule exI, auto)
  fix m1 m2 assume "P m1 m2"
  then obtain m where "P1 m1 m" and "P2 m m2" using p by metis
  obtain \<mu>1 where "apply_to_ell1 fst \<mu>1 = denotation c1 m1"
              and "apply_to_ell1 snd \<mu>1 = denotation c m"
              and "\<And>m1' m'. (m1',m') \<in> support_ell1 \<mu>1 \<longrightarrow> Q1 m1' m'";
    using `P1 m1 m` rhl1 unfolding rhoare_def by metis
  obtain \<mu>2 where "apply_to_ell1 fst \<mu>2 = denotation c m"
              and "apply_to_ell1 snd \<mu>2 = denotation c2 m2"
              and "\<And>m' m2'. (m',m2') \<in> support_ell1 \<mu>2 \<longrightarrow> Q2 m' m2'";
    using `P2 m m2` rhl2 unfolding rhoare_def by metis

  def \<mu> == "undefined::(memory*memory) ell1" (* TODO *)
  show "apply_to_ell1 fst \<mu> = denotation c1 m1" sorry
  show "apply_to_ell1 snd \<mu> = denotation c2 m2" sorry
  fix m1' m2' assume "(m1', m2') \<in> support_ell1 \<mu>"
  show "Q m1' m2'" sorry
qed

(*
TODO: (https://www.easycrypt.info/trac/raw-attachment/wiki/BibTex/Barthe.2009.POPL.pdf)
- rand (one sided)
- cond
- while
- trans
- case (+ hoare)
*)

end