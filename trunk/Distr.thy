theory Distr
imports Main Tools Extended_Sorry "~~/src/HOL/Probability/Binary_Product_Measure"
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

lemma integral_count_space_countable:
  assumes "(\<integral>\<^sup>+x. f x \<partial>count_space A) < \<infinity>"
  shows "countable {x\<in>A. f x > 0}"
proof (rule ccontr)
  assume uncountable: "uncountable {x\<in>A. f x > 0}"
  obtain \<epsilon> where "\<epsilon>>0" and "uncountable {x\<in>A. f x \<ge> \<epsilon>}" (is "uncountable ?A\<epsilon>")
  proof (atomize_elim, rule ccontr, simp)
    assume "\<forall>\<epsilon>>0. countable {x\<in>A. f x \<ge> \<epsilon>}"
    hence "countable (\<Union>n::nat. {x\<in>A. f x \<ge> 1/(Suc n)})" 
      (is "countable ?union") by auto

    have "?union \<ge> {x\<in>A. f x > 0}"
    proof (auto, case_tac "f x \<noteq> \<infinity>", auto, rule exI)
      fix x assume fx_not_inf: "f x \<noteq> \<infinity>" assume fx_pos: "0 < f x"
      def fx == "real (f x)"
      with fx_pos fx_not_inf have "fx > 0"
        by (metis zero_less_real_of_ereal) 
      have ereal_fx: "ereal fx = f x"
        by (metis `0 < fx` antisym_conv ereal_le_real_iff fx_def not_less order_refl real_le_ereal_iff) 
      def n == "floor(1/fx)"
      have "n \<ge> 0"
        unfolding n_def zero_le_floor by (metis `0 < fx` less_eq_real_def zero_le_divide_1_iff)
      have inv_mono: "\<And>a b. a>0 \<Longrightarrow> b>0 \<Longrightarrow> (a::real) \<ge> 1/b \<Longrightarrow> 1/a \<le> b"
        by (metis divide_inverse divide_le_eq_1_pos inverse_eq_divide mult.commute)
      have "n+1 \<ge> 1/fx"
        by (metis n_def real_of_int_add real_of_int_floor_add_one_ge real_of_one)
      hence ineq: "1/(n+1) \<le> fx" apply (rule_tac inv_mono[of "n+1" "fx"])
        close (metis `0 < fx` less_le_trans zero_less_divide_1_iff)
        close (metis `0 < fx`) .
      have aux1: "\<And>n. real (Suc n) = real n + 1" by auto
      have aux2: "\<And>n. n \<ge> 0 \<Longrightarrow> real (nat n) = n" by auto
      show "ereal (1 / real (Suc (nat n))) \<le> f x" 
        unfolding ereal_fx[symmetric] aux1 apply (subst aux2)
        close (fact `n\<ge>0`)
        using ineq by auto
    qed
    with `countable ?union` 
    have "countable {x\<in>A. f x > 0}"
      by (metis (no_types, lifting) countable_subset) 
    with uncountable show False ..
  qed
(*  have "count_space {x \<in> A. \<epsilon> \<le> f x} = restrict_space (count_space A) {x \<in> A. \<epsilon> \<le> f x}"
    unfolding count_space_def restrict_space_def apply auto *)
  have geq\<epsilon>: "\<And>x. max 0 (f x) \<ge> \<epsilon> * indicator ?A\<epsilon> x" 
    apply (case_tac "f x \<ge> \<epsilon>", auto)
    by (smt2 ereal_mult_zero indicator_def le_max_iff_disj max.cobounded1 monoid_mult_class.mult.right_neutral mult.commute)
  have "(\<integral>\<^sup>+x. f x \<partial>count_space A) = (\<integral>\<^sup>+x. max 0 (f x) \<partial>count_space A)"
    by (metis nn_integral_max_0)  
  also from geq\<epsilon> have "\<dots> \<ge> (\<integral>\<^sup>+x. \<epsilon> * indicator ?A\<epsilon> x \<partial>count_space A)" (is "_ \<ge> ...")
    by (rule nn_integral_mono)
  also have "\<dots> = \<epsilon> * (\<integral>\<^sup>+x. indicator ?A\<epsilon> x \<partial>count_space A)"
    apply (rule nn_integral_cmult)
    close (metis borel_measurable_count_space)
    using `\<epsilon>>0` by auto
  also have "\<dots> = \<epsilon> * emeasure (count_space A) ?A\<epsilon>"
    by (subst nn_integral_indicator, auto)
  also have "\<dots> = \<epsilon> * \<infinity>"
    apply (subst emeasure_count_space_infinite, auto)
    using `uncountable ?A\<epsilon>` by (auto simp: countable_finite)
  also have "\<dots> = \<infinity>"
    by (metis `0 < \<epsilon>` ereal_infty_mult mult.commute not_less order_refl)
  finally have "(\<integral>\<^sup>+x. f x \<partial>count_space A) = \<infinity>" by simp
  with assms show False by auto
qed

lemma support_countable: "countable (support_distr \<mu>)"
  unfolding support_distr_def
  apply (rule integral_count_space_countable[where A=UNIV and f="distr_pr \<mu>", simplified])
proof -
  have "\<And>x\<^sub>1. (\<forall>R. 0 \<le> ereal (distr_pr x\<^sub>1 R)) \<and> (\<integral>\<^sup>+ R. ereal (distr_pr x\<^sub>1 R) \<partial>count_space UNIV) \<le> 1" using Rep_distr by auto
  thus "(\<integral>\<^sup>+ x. ereal (distr_pr \<mu> x) \<partial>count_space UNIV) \<noteq> \<infinity>" by (metis (no_types) ereal_infty_less_eq(1) ereal_times(1))
qed

lemma Fubini_count_space_leq:
  assumes "\<And>x y. f x y \<ge> 0"
  shows "(\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f x y \<partial>count_space X) \<partial>count_space Y) \<le> (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f x y \<partial>count_space Y) \<partial>count_space X)"
    (is "?left \<le> ?right")
proof (cases "?right < \<infinity>")
case False thus ?thesis by auto next
case True hence "?right < \<infinity>" by auto
  from `?right < \<infinity>` have "countable {x\<in>X. (\<integral>\<^sup>+ y. f x y \<partial>count_space Y) > 0}" (is "countable ?X")
    by (rule integral_count_space_countable)
  have domX: "\<And>x y. x:X \<Longrightarrow> y:Y \<Longrightarrow> x\<notin>?X \<Longrightarrow> f x y = 0"
  proof -
    fix x y assume "x:X" "y:Y" "x\<notin>?X"
    hence "0 = (\<integral>\<^sup>+ y. f x y \<partial>count_space Y)"
      by (metis less_le mem_Collect_eq nn_integral_nonneg) 
    also have "... \<ge> (\<integral>\<^sup>+ y'. f x y' * indicator {y} y' \<partial>count_space Y)" (is "_ \<ge> ...")
      apply (rule nn_integral_mono)
      by (metis ereal_zero_mult assms indicator_def monoid_mult_class.mult.left_neutral mult.commute order_refl)
    also have "... = (\<integral>\<^sup>+ y'. f x y' \<partial>count_space {y})"
      apply (subst nn_integral_restrict_space[symmetric])
      close auto
      unfolding restrict_count_space using `y\<in>Y` by auto
    also have "\<dots> = f x y"
      by (subst nn_integral_count_space_finite, auto simp: assms max_def)
    finally show "f x y = 0" 
      using assms by (metis antisym_conv) 
  qed
  from `?right < \<infinity>` have "\<And>x. x\<in>X \<Longrightarrow> (\<integral>\<^sup>+ y. f x y \<partial>count_space Y) < \<infinity>" 
  proof (rule_tac ccontr)
    fix x0 assume "x0\<in>X" hence "x0\<in>space (count_space X)" by auto
    assume "?right < \<infinity>"
    assume "\<not> (\<integral>\<^sup>+ y. f x0 y \<partial>count_space Y) < \<infinity>"
    hence inf:"(\<integral>\<^sup>+ y. f x0 y \<partial>count_space Y) = \<infinity>" by auto
    have "?right \<ge> (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f x y \<partial>count_space Y) * indicator {x0} x \<partial>count_space X)" (is "_ \<ge> \<dots>")
      apply (rule nn_integral_mono)
      by (metis ereal_zero_times indicator_def monoid_mult_class.mult.right_neutral neq_iff nn_integral_nonneg not_less)
    also have "\<dots> = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f x y \<partial>count_space Y) \<partial>count_space {x0})"
      apply (subst nn_integral_restrict_space[symmetric])
      unfolding restrict_count_space using `x0\<in>X` by auto
    also have "\<dots> = \<infinity>"
      apply (subst nn_integral_count_space_finite, auto)
      by (metis ereal_less_eq(1) max_def inf)
    finally show False using `?right < \<infinity>` by auto
  qed
  hence "\<And>x. x\<in>X \<Longrightarrow> countable {y\<in>Y. f x y > 0}"
    by (rule integral_count_space_countable)
  with `countable ?X` have "countable (\<Union>x\<in>?X. {y\<in>Y. f x y > 0})" (is "countable ?Y")
    by auto
  have aux:"\<And>a. a\<ge>0 \<Longrightarrow> \<not> (a > 0) \<Longrightarrow> (a::ereal) = 0" by auto
  have domY: "\<And>x y. x:X \<Longrightarrow> y:Y \<Longrightarrow> y\<notin>?Y \<Longrightarrow> f x y = 0"
    apply (rule aux) close (auto simp: assms)
    apply (case_tac "x\<in>?X")
    close blast using domX by auto
  {fix y assume "y\<in>Y" have "(\<integral>\<^sup>+ x. f x y \<partial>count_space X) * indicator ?Y y = (\<integral>\<^sup>+ x. f x y \<partial>count_space X)"
  proof (cases "y\<in>?Y")
  case True thus ?thesis by auto next
  case False hence "\<And>x. x\<in>?X \<Longrightarrow> f x y = 0"
      by (smt2 `y \<in> Y` domY mem_Collect_eq)
    with domX have f0: "\<And>x. x\<in>X \<Longrightarrow> f x y = 0"
      by (smt2 `y \<in> Y`)
    show ?thesis apply (subst indicator_simps(2)) using False close simp
    apply auto using f0 by (subst nn_integral_0_iff_AE, auto)
  qed}
  hence "?left = (\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f x y \<partial>count_space X) * indicator ?Y y \<partial>count_space Y)"
    by (rule_tac nn_integral_cong, auto)
  also have "... = (\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f x y \<partial>count_space X) \<partial>count_space ?Y)"
      apply (subst nn_integral_restrict_space[symmetric]) close auto
      unfolding restrict_count_space 
      by (tactic "cong_tac 1", auto)+
  also have "\<dots> = (\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f x y * indicator ?X x \<partial>count_space X) \<partial>count_space ?Y)"
  proof (rule nn_integral_cong, rule nn_integral_cong)
    fix x y
    assume "x\<in>space(count_space X)" hence "x\<in>X" by simp
    assume "y\<in>space(count_space ?Y)" hence "y\<in>?Y" by simp
    hence "y\<in>Y" by simp
    show "f x y = f x y * indicator ?X x"
    proof (cases "x\<in>?X")
    case True thus ?thesis by simp next
    case False with `x\<in>X` `y\<in>Y` domX have "f x y = 0" by auto
      thus ?thesis by simp
    qed
  qed
  also have "\<dots> = (\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f x y \<partial>count_space ?X) \<partial>count_space ?Y)"
    apply (rule nn_integral_cong, simp)
    apply (subst nn_integral_restrict_space[symmetric]) close auto
    unfolding restrict_count_space 
    by (tactic "cong_tac 1", auto)+
  also have "\<dots> = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f x y \<partial>count_space ?Y) \<partial>count_space ?X)"
    apply (rule pair_sigma_finite.Fubini')
    unfolding pair_sigma_finite_def apply rule 
    close (fact sigma_finite_measure_count_space_countable[OF `countable ?X`])
    close (fact sigma_finite_measure_count_space_countable[OF `countable ?Y`])
    apply (subst pair_measure_countable) close (fact `countable ?X`) close (fact `countable ?Y`)
    by auto
  also have "\<dots> = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f x y * indicator ?Y y \<partial>count_space Y) \<partial>count_space ?X)" 
    apply (rule nn_integral_cong, simp)
    apply (subst nn_integral_restrict_space[symmetric]) close auto
    unfolding restrict_count_space 
    by (tactic "cong_tac 1", auto)+
  also have "\<dots> = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f x y \<partial>count_space Y) \<partial>count_space ?X)" 
  proof (rule nn_integral_cong, rule nn_integral_cong)
    fix x y
    assume "x\<in>space(count_space ?X)" hence "x\<in>?X" by simp
    hence "x\<in>X" by simp
    assume "y\<in>space(count_space Y)" hence "y\<in>Y" by simp
    show "f x y * indicator ?Y y = f x y"
    proof (cases "y\<in>?Y")
    case True thus ?thesis by simp next
    case False with `x\<in>X` `y\<in>Y` domY have "f x y = 0" by auto
      thus ?thesis by simp
    qed
  qed
  also have "\<dots> = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f x y \<partial>count_space Y) * indicator ?X x \<partial>count_space X)" 
    apply (subst nn_integral_restrict_space[symmetric]) close auto
    unfolding restrict_count_space 
    by (tactic "cong_tac 1", auto)+
  also have "\<dots> = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f x y \<partial>count_space Y) \<partial>count_space X)" 
    apply (rule_tac nn_integral_cong, auto)
    by (metis (erased, lifting) ereal_left_mult_cong indicator_def mem_Collect_eq monoid_mult_class.mult.right_neutral neq_iff nn_integral_nonneg not_less)
  finally show "?left \<le> ?right" by simp
qed
  

lemma Fubini_count_space:
  "(\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f x y \<partial>count_space X) \<partial>count_space Y) = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f x y \<partial>count_space Y) \<partial>count_space X)"
    (is "?left = ?right")
proof -
  let ?f = "\<lambda>x y. max 0 (f x y)"
  have left: "?left = (\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. ?f x y \<partial>count_space X) \<partial>count_space Y)"
    (is "_ = ?left0")
    by (metis nn_integral_max_0)
  have right: "?right = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. ?f x y \<partial>count_space Y) \<partial>count_space X)"
    (is "_ = ?right0")
    by (metis nn_integral_max_0)
  have "?left0 \<le> ?right0"
    by (rule Fubini_count_space_leq, auto)
  moreover have "?left0 \<ge> ?right0"
    by (rule Fubini_count_space_leq, auto)
  ultimately have "?left0 = ?right0" by simp
  with left right
  show ?thesis by auto
qed

lemma nn_integral_counting_single:
  assumes "x\<in>X"
  shows "f x \<le> \<integral>\<^sup>+x. f x \<partial>count_space X"
proof -
  have "(\<integral>\<^sup>+x. f x \<partial>count_space X) = \<integral>\<^sup>+x. max 0 (f x) \<partial>count_space X"
    by (metis nn_integral_max_0)
  also have "... \<ge> \<integral>\<^sup>+x'. max 0 (f x') * indicator {x} x' \<partial>count_space X" (is "_ \<ge> ...")
    apply (rule nn_integral_mono) unfolding indicator_def by auto
  also have "\<dots> = \<integral>\<^sup>+x'. max 0 (f x') \<partial>count_space {x}"
    apply (subst nn_integral_restrict_space[symmetric])
    close auto
    unfolding restrict_count_space using assms by auto
  also have "\<dots> = max 0 (f x)"
    by (subst nn_integral_count_space_finite, auto)
  finally show ?thesis using assms by auto
qed

definition compose_distr :: "('a \<Rightarrow> 'b distr) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" where
  "compose_distr f \<mu> == Abs_distr (\<lambda>b. real (\<integral>\<^sup>+a. Rep_distr \<mu> a * Rep_distr (f a) b \<partial>count_space UNIV))"
lemma compose_distr_pr: "distr_pr (compose_distr f \<mu>) b =
  real (\<integral>\<^sup>+a. distr_pr \<mu> a * distr_pr (f a) b \<partial>count_space UNIV)"
proof -
  have aux1: "\<And>a b::ereal. a\<ge>0 \<Longrightarrow> b\<le>1 \<Longrightarrow> a*b \<le> a"
    by (metis ereal_mult_right_mono monoid_mult_class.mult.left_neutral mult.commute) 
  have nn_integral_counting_single_aux: "\<And>x X f. x\<in>X \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>count_space X) < \<infinity> \<Longrightarrow> f x < \<infinity>"
    by (metis ereal_infty_less(1) nn_integral_counting_single not_less)
    
  have "(\<integral>\<^sup>+ b. \<integral>\<^sup>+ a. ereal (distr_pr \<mu> a * distr_pr (f a) b)
            \<partial>count_space UNIV \<partial>count_space UNIV) =
        (\<integral>\<^sup>+ a. \<integral>\<^sup>+ b. ereal (distr_pr \<mu> a * distr_pr (f a) b)
            \<partial>count_space UNIV \<partial>count_space UNIV)" (is "?int_ba = ?int_ab")
    by (rule Fubini_count_space)
  also have "... = (\<integral>\<^sup>+ a. ereal (distr_pr \<mu> a) * \<integral>\<^sup>+ b. ereal (distr_pr (f a) b)
            \<partial>count_space UNIV \<partial>count_space UNIV)"
    by (subst nn_integral_cmult[symmetric], auto simp: distr_pr_geq0)
  also have "... \<le> (\<integral>\<^sup>+ a. ereal (distr_pr \<mu> a) \<partial>count_space UNIV)"
    apply (rule nn_integral_mono, auto, rule aux1)
    close (metis distr_pr_geq0 ereal_less_eq(5))
    using Rep_distr by auto
  also have "\<dots> \<le> 1"
    using Rep_distr by auto
  finally have "?int_ba \<le> 1" by simp
  with `?int_ba = ?int_ab` have "?int_ab \<le> 1" by simp
  have int_b:"\<And>a. (\<integral>\<^sup>+ b. ereal (distr_pr \<mu> b * distr_pr (f b) a) \<partial>count_space UNIV) < \<infinity>"
    apply (rule_tac x=a and X=UNIV in nn_integral_counting_single_aux, auto)
    using `?int_ba \<le> 1`
    by (metis PInfty_neq_ereal(1) ereal_infty_less_eq(1) one_ereal_def)
  show ?thesis
    unfolding compose_distr_def apply (subst Abs_distr_inverse, auto)
    apply (metis nn_integral_nonneg real_of_ereal_pos)
    apply (subst ereal_real')
    using int_b close auto
    using `?int_ba \<le> 1` .
qed

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
