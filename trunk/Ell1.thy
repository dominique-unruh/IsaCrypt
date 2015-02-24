theory Ell1
imports Main Setsum_Infinite Real_Vector_Spaces Complete_Lattices
begin

section {* ell1 (absolutely convergent real series) *}
typedef 'a ell1 = "{\<mu>::'a\<Rightarrow>real. SetSums (\<lambda>x. abs(\<mu> x)) UNIV}"
  apply (rule exI[of _ "\<lambda>x. 0"], auto) unfolding SetSums_def
  using setsum_0 by auto

instantiation ell1 :: (type) zero begin
definition zero_ell1 :: "'a ell1" where "zero_ell1 = Abs_ell1 (\<lambda>x. 0)";
instance ..
end

instantiation ell1 :: (type) comm_monoid_add begin
definition "\<mu> + \<nu> = Abs_ell1 (\<lambda>x. Rep_ell1 \<mu> x + Rep_ell1 \<nu> x)"
instance apply intro_classes sorry
end

instantiation ell1 :: (type) real_vector begin
definition "\<mu> - \<nu> = Abs_ell1 (\<lambda>x. Rep_ell1 \<mu> x - Rep_ell1 \<nu> x)"
definition "-(\<nu>::'a ell1) = 0-\<nu>"
definition "scaleR r (\<mu>::'a ell1) = Abs_ell1 (\<lambda>x. r * Rep_ell1 \<mu> x)" 
instance apply intro_classes sorry
end

instantiation ell1 :: (type) real_normed_vector begin
definition "norm_ell1 (s::'a ell1) = SetSum (\<lambda>x. abs(Rep_ell1 s x)) UNIV"
definition "dist_ell1 (s::'a ell1) t = norm (s-t)"
definition "open_ell1 (S::'a ell1 set) = (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"
definition "sgn_ell1 (s::'a ell1) = s /\<^sub>R norm s"
instance apply intro_classes sorry
end

instantiation ell1 :: (type) order begin
definition "s \<le> (t::'a ell1) = (\<forall>x. Rep_ell1 s x \<le> Rep_ell1 t x)"
definition "s < (t::'a ell1) = (s \<le> t \<and> s \<noteq> t)"
instance apply intro_classes sorry
end

instantiation ell1 :: (type) ordered_real_vector begin
instance apply intro_classes sorry
end

definition "weight_ell1 \<mu> = SetSum (\<lambda>x. Rep_ell1 \<mu> x) UNIV"

definition point_ell1 :: "'a \<Rightarrow> 'a ell1" where "point_ell1 a = Abs_ell1 (\<lambda>x. if x=a then 1 else 0)";
lemma weight_point_ell1 [simp]: "weight_ell1 (point_ell1 x) = 1"
  sorry

consts compose_ell1 :: "('a \<Rightarrow> 'b ell1) \<Rightarrow> 'a ell1 \<Rightarrow> 'b ell1";
definition apply_to_ell1 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ell1 \<Rightarrow> 'b ell1" where
  "apply_to_ell1 f = compose_ell1 (\<lambda>x. point_ell1 (f x))"
definition "support_ell1 \<mu> = {x. Rep_ell1 \<mu> x \<noteq> 0}"

lemma apply_to_ell1_twice [simp]: "apply_to_ell1 f (apply_to_ell1 g \<mu>) = apply_to_ell1 (\<lambda>x. f (g x)) \<mu>"
  sorry

lemma apply_to_ell1_id [simp]: "apply_to_ell1 (\<lambda>x. x) \<mu> = \<mu>"
  sorry

lemma support_compose_ell1 [simp]: "support_ell1 (compose_ell1 f g) = (\<Union>x\<in>support_ell1 g. support_ell1 (f x))"
  sorry

lemma support_apply_to_ell1 [simp]: "support_ell1 (apply_to_ell1 f \<mu>) = f ` support_ell1 \<mu>"
  sorry

lemma support_point_ell1 [simp]: "support_ell1 (point_ell1 x) = {x}"
  sorry

definition "product_ell1 \<mu> \<nu> = Abs_ell1 (\<lambda>(x,y). Rep_ell1 \<mu> x * Rep_ell1 \<nu> y)"
lemma fst_product_ell1 [simp]: "apply_to_ell1 fst (product_ell1 \<mu> \<nu>) = weight_ell1 \<nu> *\<^sub>R \<mu>"
  sorry
lemma snd_product_ell1 [simp]: "apply_to_ell1 snd (product_ell1 \<mu> \<nu>) = weight_ell1 \<mu> *\<^sub>R \<nu>"
  sorry
lemma support_product_ell1 [simp]: "support_ell1 (product_ell1 \<mu> \<nu>) = support_ell1 \<mu> \<times> support_ell1 \<nu>"
  sorry
lemma product_ell1_sym: "apply_to_ell1 (\<lambda>(x,y). (y,x)) (product_ell1 \<mu> \<nu>) = product_ell1 \<nu> \<mu>"
  sorry

section {* Distributions (with weight \<le> 1) *}

typedef 'a distr = "{\<mu>::'a\<Rightarrow>real. (\<forall>x. \<mu> x\<ge>0) \<and> (\<exists>b\<le>1. SetSums_to \<mu> UNIV b)}"
  apply (rule exI[where x="\<lambda>x. 0"], auto) unfolding SetSums_def
  apply (rule exI[where x=0])
  using setsum_0 by auto

definition support_distr :: "'a distr \<Rightarrow> 'a set" where
  "support_distr \<mu> = {x. Rep_distr \<mu> x > 0}"
instantiation distr :: (type) zero begin
definition zero_distr :: "'a distr" where "zero_distr = Abs_distr (\<lambda>x. 0)";
instance ..
end
definition point_distr :: "'a \<Rightarrow> 'a distr" where "point_distr a = Abs_distr (\<lambda>x. if x=a then 1 else 0)";
consts compose_distr :: "('a \<Rightarrow> 'b distr) \<Rightarrow> 'a distr \<Rightarrow> 'b distr";
definition apply_to_distr :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" where
  "apply_to_distr f = compose_distr (\<lambda>x. point_distr (f x))"


definition uniform :: "'a set \<Rightarrow> 'a distr" where
  "uniform S = Abs_distr (\<lambda>x. if x \<in> S then 1/(card S) else 0)"

section {* Combining ell1 and distr *}

definition "distr_to_ell1 \<mu> = Abs_ell1 (Rep_distr \<mu>)"

lemma distr_to_ell1_apply_comm [simp]: "distr_to_ell1 (apply_to_distr f \<mu>) = apply_to_ell1 f (distr_to_ell1 \<mu>)"
  sorry
lemma support_distr_apply [simp]: "support_distr (apply_distr f \<mu>) = f ` (support_distr \<mu>)"
  sorry

end
