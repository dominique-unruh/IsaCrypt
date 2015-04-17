theory Distr
imports Main Tools Extended_Sorry "~~/src/HOL/Probability/Nonnegative_Lebesgue_Integration"
begin

subsection {* Distributions (with weight <= 1) *}

typedef 'a distr = "{\<mu>::'a\<Rightarrow>real. (\<forall>x. (\<mu> x)\<ge>0) \<and> (\<integral>\<^sup>+x. \<mu> x \<partial>count_space UNIV) \<le> 1}"
  apply (rule exI[where x="\<lambda>x. 0"], auto)
  by (metis ereal_eq_0(2) ereal_less_eq(6) ereal_zero_mult zero_le_one)

abbreviation "distr_pr == Rep_distr"
lemma distr_pr_geq0: "distr_pr \<mu> x \<ge> 0"
  using Rep_distr[of \<mu>] by auto 

definition support_distr :: "'a distr \<Rightarrow> 'a set" where
  "support_distr \<mu> = {x. Rep_distr \<mu> x > 0}"

instantiation distr :: (type) zero begin
definition zero_distr :: "'a distr" where "zero_distr = Abs_distr (\<lambda>x. 0)";
instance ..
end

instantiation distr :: (type) scaleR begin
definition "scaleR_distr r \<mu> = Abs_distr (\<lambda>x. r * Rep_distr \<mu> x)"
instance ..
end

lemma scaleR_one_distr: "1 *\<^sub>R (\<mu>::'a distr) = \<mu>"
  unfolding scaleR_distr_def using Rep_distr_inverse by auto  

definition "weight_distr \<mu> = real (\<integral>\<^sup>+x. Rep_distr \<mu> x \<partial>count_space UNIV)"

lemma ereal_indicator: "\<And>x. ereal (indicator {a} x) = indicator {a} x" unfolding indicator_def by auto


definition point_distr :: "'a \<Rightarrow> 'a distr" where "point_distr a = Abs_distr (indicator {a})";
lemma weight_point_distr [simp]: "weight_distr (point_distr a) = 1"
proof - 
  note[[show_consts]]
  have sum1: "(\<integral>\<^sup>+ x. ereal (indicator {a} x) \<partial>count_space UNIV) = 1"
    unfolding ereal_indicator
    by (subst nn_integral_indicator, auto)
  show ?thesis
    unfolding weight_distr_def point_distr_def 
    by (subst Abs_distr_inverse, auto simp: sum1)
qed

lemma point_distr_pr [simp]: "distr_pr (point_distr a) x = (if x=a then 1 else 0)"
proof -
  have sum1: "(\<integral>\<^sup>+ x. ereal (indicator {a} x) \<partial>count_space UNIV) = 1"
    unfolding ereal_indicator
    by (subst nn_integral_indicator, auto)
  show ?thesis
    unfolding point_distr_def 
    by (subst Abs_distr_inverse, auto simp: sum1) 
qed

definition compose_distr :: "('a \<Rightarrow> 'b distr) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" where
  "compose_distr f \<mu> == Abs_distr (\<lambda>b. real (\<integral>\<^sup>+a. Rep_distr \<mu> a * Rep_distr (f a) b \<partial>count_space UNIV))"
definition apply_to_distr :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" where
  "apply_to_distr f \<mu> = Abs_distr (\<lambda>b. real (\<integral>\<^sup>+a. Rep_distr \<mu> a * indicator {f a} b \<partial>count_space UNIV))"

lemma compose_point_distr_r [simp]: "compose_distr f (point_distr x) = f x"
proof -
  have rw: "\<And>y b. ereal ((if y = x then 1 else 0) * distr_pr (f y) b) =
                  ereal (distr_pr (f x) b) * indicator {x} y"
    by simp
  show ?thesis
    unfolding compose_distr_def 
    apply simp unfolding rw
    apply (subst nn_integral_cmult_indicator)
    close (simp add: distr_pr_geq0)
    close simp
    by (simp add: Rep_distr_inverse)
qed

lemma compose_point_distr_l [simp]: "compose_distr (\<lambda>x. point_distr (f x)) \<mu> = apply_to_distr f \<mu>"
  unfolding compose_distr_def point_distr_def apply_to_distr_def
  apply (subst Abs_distr_inverse, auto)
  by (subst ereal_indicator, auto)

lemma apply_to_distr_twice [simp]: "apply_to_distr f (apply_to_distr g \<mu>) = apply_to_distr (\<lambda>x. f (g x)) \<mu>"
  SORRY

lemma apply_to_distr_id [simp]: "apply_to_distr (\<lambda>x. x) \<mu> = \<mu>"
proof -
  have rew1: "\<And>x b. ereal (distr_pr \<mu> x) * indicator {x} b = ereal (distr_pr \<mu> b) * indicator {b} x"
    by (case_tac "x=b", auto)
  show ?thesis
    unfolding apply_to_distr_def compose_distr_def point_distr_pr
    unfolding ereal_mult_indicator rew1 
    apply (subst nn_integral_cmult_indicator, auto simp: distr_pr_geq0)
    by (rule Rep_distr_inverse)
qed

lemma support_compose_distr [simp]: "support_distr (compose_distr f g) = (\<Union>x\<in>support_distr g. support_distr (f x))"
  SORRY

lemma support_apply_to_distr [simp]: "support_distr (apply_to_distr f \<mu>) = f ` support_distr \<mu>"
  SORRY

lemma support_point_distr [simp]: "support_distr (point_distr x) = {x}"
  unfolding support_distr_def by simp

definition "product_distr \<mu> \<nu> = Abs_distr (\<lambda>(x,y). Rep_distr \<mu> x * Rep_distr \<nu> y)"
lemma product_distr_pr: "distr_pr (product_distr \<mu> \<nu>) (x,y) = distr_pr \<mu> x * distr_pr \<nu> y"
  SORRY
lemma fst_product_distr [simp]: "apply_to_distr fst (product_distr \<mu> \<nu>) = weight_distr \<nu> *\<^sub>R \<mu>"
  SORRY
lemma snd_product_distr [simp]: "apply_to_distr snd (product_distr \<mu> \<nu>) = weight_distr \<mu> *\<^sub>R \<nu>"
  SORRY
lemma support_product_distr [simp]: "support_distr (product_distr \<mu> \<nu>) = support_distr \<mu> \<times> support_distr \<nu>"
  unfolding support_distr_def
  apply auto unfolding product_distr_pr
  close (metis distr_pr_geq0 less_eq_real_def mult_zero_left)
  close (metis distr_pr_geq0 less_eq_real_def mult_zero_right)
  by simp
lemma product_distr_sym: "apply_to_distr (\<lambda>(x,y). (y,x)) (product_distr \<mu> \<nu>) = product_distr \<nu> \<mu>"
  SORRY

lemma apply_to_point_distr [simp]: "apply_to_distr f (point_distr x) = point_distr (f x)"
  unfolding compose_point_distr_l[symmetric] compose_point_distr_r ..

lemma point_distr_inj: "point_distr x = point_distr y \<Longrightarrow> x = y"
proof -
  assume "point_distr x = point_distr y"
  hence "support_distr (point_distr x) = support_distr (point_distr y)" by simp
  hence "{x} = {y}" by simp
  thus "x=y" by simp
qed

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


lemma compose_distr_assoc: "compose_distr (\<lambda>x. compose_distr g (f x)) \<mu> = compose_distr g (compose_distr f \<mu>)" 
  SORRY

(*
subsection {* Combining ell1 and distr *}

definition "distr_to_ell1 \<mu> = Abs_ell1 (Rep_distr \<mu>)"
definition "ell1_to_distr \<mu> = Abs_distr (Rep_ell1 \<mu>)"

lemma distr_to_ell1_apply_comm [simp]: "distr_to_ell1 (apply_to_distr f \<mu>) = apply_to_ell1 f (distr_to_ell1 \<mu>)"
  sorry
lemma support_distr_to_ell1 [simp]: "support_ell1 (distr_to_ell1 \<mu>) = support_distr \<mu>"
  sorry
*)


end
