theory Ell1
imports Main Tools Setsum_Infinite Real_Vector_Spaces Complete_Lattices "~~/src/HOL/Probability/Binary_Product_Measure" 
begin

subsection {* ell1 (absolutely convergent real series) *}
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

lemma apply_to_point_ell1 [simp]: "apply_to_ell1 f (point_ell1 x) = point_ell1 (f x)"
  sorry
lemma point_ell1_inj: "point_ell1 x = point_ell1 y \<Longrightarrow> x = y"
  sorry


subsection {* Distributions (with weight <= 1) *}

typedef 'a distr = "{M::'a measure. emeasure M (space M) \<le> 1 \<and> space M = UNIV \<and> sets M = UNIV}"
  by (rule exI[of _ "sigma UNIV UNIV"], auto simp: emeasure_sigma)
definition "distr_pre d == emeasure (Rep_distr d)"
definition "distr_pr d == measure (Rep_distr d)"
abbreviation "distr_pr1 d x == distr_pr d {x}"

definition support_distr :: "'a distr \<Rightarrow> 'a set" where
  "support_distr \<mu> = {x. distr_pr1 \<mu> x > 0}"

instantiation distr :: (type) zero begin
definition zero_distr :: "'a distr" where "zero_distr = Abs_distr (sigma UNIV UNIV)";
instance ..
end

instantiation distr :: (type) scaleR begin
definition "scaleR_distr r \<mu> = Abs_distr (measure_of 
  (space (Rep_distr \<mu>)) (sets (Rep_distr \<mu>)) (\<lambda>E. ereal r * emeasure (Rep_distr \<mu>) E))"
instance ..
end

lemma scaleR_one_distr [simp]: "1 *\<^sub>R (\<mu>::'a distr) = \<mu>"
  unfolding scaleR_distr_def one_ereal_def[symmetric]
  by (auto simp: measure_of_of_measure Rep_distr_inverse)

abbreviation "weight_distr \<mu> == distr_pr \<mu> UNIV"

lemma Rep_Abs_distr_measure_of: "X UNIV \<le> 1 \<Longrightarrow> Rep_distr (Abs_distr (measure_of UNIV UNIV X)) = measure_of UNIV UNIV X"
  apply (subst Abs_distr_inverse) by (auto simp: emeasure_measure_of_conv)

definition "mk_distr (f::_\<Rightarrow>real) == Abs_distr (measure_of UNIV UNIV f)"
definition "mk_distre (f::_\<Rightarrow>ereal) == Abs_distr (measure_of UNIV UNIV f)"
print_theorems
lemma mk_distre_pr: 
  assumes "f UNIV \<le> 1"
  assumes "\<And>x. f x \<ge> 0"
  assumes "f {} = 0"
  assumes "\<And>A. disjoint_family A \<Longrightarrow> (\<Sum>i. f (A i)) = f (\<Union>i. A i)"
  shows "distr_pre (mk_distre f) = f"
proof -
  have sigma_UNIV: "sigma_sets UNIV UNIV = UNIV"
    by (metis UNIV_eq_I iso_tuple_UNIV_I sigma_sets.Basic)
  have "measure_space UNIV (sigma_sets UNIV UNIV) f"
    unfolding measure_space_def apply auto
    apply (metis Pow_UNIV sigma_algebra_sigma_sets top_greatest)
    unfolding positive_def using assms close auto
    unfolding sigma_UNIV countably_additive_def
    using assms by auto
  thus ?thesis
    unfolding mk_distre_def distr_pre_def
    apply (subst Abs_distr_inverse) 
    by (auto simp: emeasure_measure_of_conv assms)
qed

lemma mk_distr_pr: 
  assumes "f UNIV \<le> 1"
  assumes "\<And>x. f x \<ge> 0"
  assumes "f {} = 0"
  assumes "\<And>A. disjoint_family A \<Longrightarrow> (\<Sum>i. f (A i)) = f (\<Union>i. A i)"
  shows "distr_pr (mk_distr f) = f"
sorry

definition point_distr :: "'a \<Rightarrow> 'a distr" where
  "point_distr a = mk_distr (\<lambda>E. if a\<in>E then 1 else 0)";
lemma point_distr_pr: "distr_pr (point_distr a) E = (if a\<in>E then 1 else 0)"
  unfolding point_distr_def apply (subst mk_distr_pr, auto)
  sorry
lemma weight_point_distr [simp]: "weight_distr (point_distr x) = 1"
  unfolding point_distr_pr by simp

definition compose_distr :: "('a \<Rightarrow> 'b distr) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" where
  "compose_distr f \<mu> == mk_distre (\<lambda>E. (\<integral>\<^sup>+ a. distr_pre (f a) E \<partial>Rep_distr \<mu>))"
definition apply_to_distr :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" where
  "apply_to_distr f \<mu> = Abs_distr (distr (Rep_distr \<mu>) (sigma UNIV UNIV) f)"

lemma [simp]: "space (Rep_distr \<mu>) = UNIV"
  using Rep_distr[of \<mu>] by auto
lemma [simp]: "sets (Rep_distr \<mu>) = UNIV"
  using Rep_distr[of \<mu>] by auto

lemma apply_to_distr_twice [simp]: "apply_to_distr f (apply_to_distr g \<mu>) = apply_to_distr (\<lambda>x. f (g x)) \<mu>"
proof -
  let ?\<mu> = "Rep_distr \<mu>"
  have valid: "emeasure (distr (Rep_distr \<mu>) (sigma UNIV UNIV) g) UNIV \<le> 1" sorry
  show ?thesis
    unfolding apply_to_distr_def
    apply (subst Abs_distr_inverse, auto simp: valid)
    apply (subst distr_distr)
    unfolding measurable_def o_def
    by (auto intro: Rep_distr)
qed

lemma apply_to_distr_id [simp]: "apply_to_distr (\<lambda>x. x) \<mu> = \<mu>"
proof -
  let ?\<mu> = "Rep_distr \<mu>"
  have "?\<mu> = distr ?\<mu> ?\<mu> (\<lambda>x .x)" using distr_id by auto
  moreover have "... = distr ?\<mu> (sigma UNIV UNIV) (\<lambda>x. x)"
    by (rule distr_cong, auto)
  finally have eq:"... = ?\<mu>" by simp
  show ?thesis
    unfolding apply_to_distr_def unfolding eq
    by (rule Rep_distr_inverse)
qed

lemma support_compose_distr [simp]: "support_distr (compose_distr f g) = (\<Union>x\<in>support_distr g. support_distr (f x))"
  sorry

lemma support_apply_to_distr [simp]: "support_distr (apply_to_distr f \<mu>) = f ` support_distr \<mu>"
  sorry

lemma support_point_distr [simp]: "support_distr (point_distr x) = {x}"
  sorry

definition "product_distr \<mu> \<nu> = Abs_distr (Rep_distr \<mu>  \<Otimes>\<^sub>M  Rep_distr \<nu>)"

lemma [simp]: "sigma_finite_measure (Rep_distr \<mu>)"
  unfolding sigma_finite_measure_def apply (rule exI[of _ "{UNIV}"])
  apply auto using Rep_distr
  by (metis (full_types, lifting) ereal_infty_less_eq(1) ereal_times(1) mem_Collect_eq) 

lemma fst_product_distr [simp]: "apply_to_distr fst (product_distr \<mu> \<nu>) = weight_distr \<nu> *\<^sub>R \<mu>"
  sorry
lemma snd_product_distr [simp]: "apply_to_distr snd (product_distr \<mu> \<nu>) = weight_distr \<mu> *\<^sub>R \<nu>"
  sorry
lemma support_product_distr [simp]: "support_distr (product_distr \<mu> \<nu>) = support_distr \<mu> \<times> support_distr \<nu>"
  sorry
lemma product_distr_sym: "apply_to_distr (\<lambda>(x,y). (y,x)) (product_distr \<mu> \<nu>) = product_distr \<nu> \<mu>"
proof -
  have \<mu>1: "emeasure (Rep_distr \<mu>) UNIV \<le> 1" and \<nu>1: "emeasure (Rep_distr \<nu>) UNIV \<le> 1" using Rep_distr by auto
  have 11: "1::ereal == 1 * 1" by auto
  have mult_mono: "\<And>a b c d. a\<le>c \<Longrightarrow> b\<le>d \<Longrightarrow> b\<ge>0 \<Longrightarrow> c\<ge>0 \<Longrightarrow> (a::ereal) * b \<le> c * d"
    by (metis ereal_mult_left_mono mult.commute order_trans)
  have leq1: "emeasure (Rep_distr \<mu>) UNIV * emeasure (Rep_distr \<nu>) UNIV \<le> 1"
    apply (subst 11) apply (rule mult_mono) using Rep_distr by auto
  have leq1': "emeasure (Rep_distr \<mu> \<Otimes>\<^sub>M Rep_distr \<nu>) UNIV \<le> 1"
    apply (subst UNIV_Times_UNIV[symmetric])
    unfolding space_pair_measure apply simp
    apply (subst UNIV_Times_UNIV[symmetric])
    by (subst sigma_finite_measure.emeasure_pair_measure_Times, auto simp: leq1)
  show ?thesis 
    unfolding apply_to_distr_def product_distr_def
    apply (subst Abs_distr_inverse)
    apply (auto simp: leq1' space_pair_measure sets_pair_measure)
    find_theorems "sigma_sets UNIV" sorry

by
UNIV_Times_UNIV
  let ?\<mu> = "Rep_distr \<mu>" let ?\<nu> = "Rep_distr \<nu>"
apply  distr_pair_swap
  sorry

lemma apply_to_point_distr [simp]: "apply_to_distr f (point_distr x) = point_distr (f x)"
  sorry
lemma point_distr_inj: "point_distr x = point_distr y \<Longrightarrow> x = y"
  sorry


definition uniform :: "'a set \<Rightarrow> 'a distr" where
  "uniform S = Abs_distr (\<lambda>x. if x \<in> S then 1/(card S) else 0)"


lemma markov_chain:
  assumes "apply_to_distr snd \<mu>1 = apply_to_distr fst \<mu>2"
  obtains \<mu> where "apply_to_distr (\<lambda>(x::'a,y::'b,z::'c). (x,y)) \<mu> = \<mu>1" 
              and "apply_to_distr (\<lambda>(x,y,z). (y,z)) \<mu> = \<mu>2"
proof
  def \<mu> == "undefined::('a*'b*'c) distr"
  show "apply_to_distr (\<lambda>(x,y,z). (x,y)) \<mu> = \<mu>1" sorry
  show "apply_to_distr (\<lambda>(x,y,z). (y,z)) \<mu> = \<mu>2" sorry
qed

lemma compose_point_distr_r [simp]: "compose_distr f (point_distr x) = f x"
  sorry
lemma compose_point_distr_l [simp]: "compose_distr (\<lambda>x. point_distr (f x)) \<mu> = apply_to_distr f \<mu>"
  unfolding apply_to_distr_def ..

lemma compose_distr_trans: "compose_distr (\<lambda>x. compose_distr g (f x)) \<mu> = compose_distr g (compose_distr f \<mu>)" 
  sorry  

subsection {* Combining ell1 and distr *}

definition "distr_to_ell1 \<mu> = Abs_ell1 (Rep_distr \<mu>)"
definition "ell1_to_distr \<mu> = Abs_distr (Rep_ell1 \<mu>)"

lemma distr_to_ell1_apply_comm [simp]: "distr_to_ell1 (apply_to_distr f \<mu>) = apply_to_ell1 f (distr_to_ell1 \<mu>)"
  sorry
lemma support_distr_to_ell1 [simp]: "support_ell1 (distr_to_ell1 \<mu>) = support_distr \<mu>"
  sorry



end
