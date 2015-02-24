theory RHL_Untyped
imports Lang_Untyped 
begin

definition rhoare :: "(memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> program \<Rightarrow> (memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "rhoare pre c1 c2 post =
  (\<forall>m1 m2. pre m1 m2 \<longrightarrow> 
     (\<exists>\<mu>. apply_to_ell1 fst \<mu> = denotation c1 m1
        \<and> apply_to_ell1 snd \<mu> = denotation c2 m1
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

(*
TODO:
- ass
- rand (+ hoare)
- cond
- while
- sym
- trans
- case (+ hoare)
*)

end