theory Distr
imports Main Tools Extended_Sorry "~~/src/HOL/Probability/Binary_Product_Measure"
begin

lemma nn_integral_pos:
  assumes "(\<integral>\<^sup>+x. f x \<partial>\<mu>) > 0"
  shows "\<exists>x. f x > 0" (* \<and> \<mu> {x} > 0 *)
proof -
  have "(\<And>x. f x \<le> 0) \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>\<mu>) = 0"
    by (metis ereal_zero_times nn_integral_cong_pos nn_integral_const order_refl)
  with assms show ?thesis
    using le_less_linear by fastforce 
qed

lemma nn_integral_singleton_indicator:
  assumes "f y \<ge> 0"
  assumes "{y} \<in> sets \<mu>"
  shows "(\<integral>\<^sup>+x. f x * indicator {y} x \<partial>\<mu>) = f y * emeasure \<mu> {y}"
proof -
  have "(\<integral>\<^sup>+x. f x * indicator {y} x \<partial>\<mu>) = (\<integral>\<^sup>+x. f y * indicator {y} x \<partial>\<mu>)"
    by (metis ereal_zero_times indicator_simps(2) singletonD)
  also have "... = f y * emeasure \<mu> {y}"
    apply (rule nn_integral_cmult_indicator)  
    using assms by auto
  finally show ?thesis .
qed

lemma nn_integral_singleton_indicator_countspace:
  assumes "f y \<ge> 0" and "y \<in> M"
  shows "(\<integral>\<^sup>+x. f x * indicator {y} x \<partial>count_space M) = f y"
apply (subst nn_integral_singleton_indicator)
  using assms apply auto
  by (metis mult.comm_neutral one_ereal_def)

(* lemma nn_integral_count_space_geq_single:
  assumes "x \<in> M" and "\<And>x. f x \<ge> 0" 
  shows "(\<integral>\<^sup>+y. f y \<partial>count_space M) \<ge> f x"
proof (cases "f x \<ge> 0")
  assume fx: "f x \<ge> 0"
  have "(\<integral>\<^sup>+y. f y \<partial>count_space M) \<ge> (\<integral>\<^sup>+y. f y * indicator {x} y \<partial>count_space M)"
    apply (rule nn_integral_mono) 
    apply (thin_tac _)
    unfolding indicator_def
    using fx apply auto
 *)


typedef 'a distr = "{\<mu>::'a\<Rightarrow>real. (\<forall>x. (\<mu> x)\<ge>0) \<and> (\<integral>\<^sup>+x. \<mu> x \<partial>count_space UNIV) \<le> 1}"
  apply (rule exI[where x="\<lambda>x. 0"], auto)
  by (metis ereal_eq_0(2) ereal_less_eq(6) ereal_zero_mult zero_le_one)

(* abbreviation "Rep_distr == Rep_distr" *)
lemma Rep_distr_geq0: "Rep_distr \<mu> x \<ge> 0"
  using Rep_distr[of \<mu>] by auto 

lemma Rep_distr_int_leq1: "(\<integral>\<^sup>+x. Rep_distr \<mu> x \<partial>count_space UNIV) \<le> 1"
  using Rep_distr[of \<mu>] by auto

definition support_distr :: "'a distr \<Rightarrow> 'a set" where
  "support_distr \<mu> = {x. Rep_distr \<mu> x > 0}"

instantiation distr :: (type) zero begin
definition zero_distr :: "'a distr" where "zero_distr = Abs_distr (\<lambda>x. 0)"
instance ..
end

instantiation distr :: (type) scaleR begin
definition "scaleR_distr r \<mu> = Abs_distr (\<lambda>x. r * Rep_distr \<mu> x)"
instance ..
end

lemma Rep_distr_scaleR: "r \<ge> 0 \<Longrightarrow> r \<le> 1 \<Longrightarrow> Rep_distr (r *\<^sub>R \<mu>) x = r * Rep_distr \<mu> x"
proof -
  assume rpos: "r \<ge> 0" and rleq1: "r \<le> 1"
  have pos: "\<And>x. 0 \<le> r * Rep_distr \<mu> x"
    by (simp add: Rep_distr_geq0 rpos)
  have "(\<integral>\<^sup>+ x. ereal (r * Rep_distr \<mu> x) \<partial>count_space UNIV) = r * (\<integral>\<^sup>+ x. ereal (Rep_distr \<mu> x) \<partial>count_space UNIV)"
    unfolding times_ereal.simps(1)[symmetric]
    apply (subst nn_integral_cmult)
    using rpos by auto
  also have "\<dots> \<le> ereal r * 1"
    apply (rule ereal_mult_left_mono)
    close (rule Rep_distr_int_leq1)
    using rpos by auto
  also have "\<dots> \<le> 1"
    using rleq1 by auto
  finally have leq1: "(\<integral>\<^sup>+ x. ereal (r * Rep_distr \<mu> x) \<partial>count_space UNIV) \<le> 1" by assumption
  show ?thesis
    unfolding scaleR_distr_def
    apply (subst Abs_distr_inverse)
    using pos leq1 by auto
qed
lemma scaleR_one_distr: "1 *\<^sub>R (\<mu>::'a distr) = \<mu>"
  unfolding scaleR_distr_def using Rep_distr_inverse by auto  

definition "probability \<mu> E = real (\<integral>\<^sup>+x. Rep_distr \<mu> x * (if E x then 1 else 0) \<partial>count_space UNIV)" 

definition "weight_distr \<mu> = real (\<integral>\<^sup>+x. Rep_distr \<mu> x \<partial>count_space UNIV)"
lemma weight_distr_pos: "weight_distr \<mu> \<ge> 0"
  by (simp add: nn_integral_nonneg real_of_ereal_pos weight_distr_def) 
lemma weight_distr_leq1: "weight_distr \<mu> \<le> 1"
  unfolding weight_distr_def by (simp add: Rep_distr_int_leq1 real_of_ereal_le_1) 

(* lemma ereal_indicator: "\<And>x. ereal (indicator {a} x) = indicator {a} x" unfolding indicator_def by auto *)


definition point_distr :: "'a \<Rightarrow> 'a distr" where "point_distr a = Abs_distr (indicator {a})"
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

lemma Rep_point_distr [simp]: "Rep_distr (point_distr a) x = (if x=a then 1 else 0)"
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
    proof - (* sledgehammer proof *)
      fix x :: 'a
      assume "\<epsilon> \<le> f x"
      hence "\<epsilon> \<le> max 0 (f x)" by (metis (no_types) max.bounded_iff max_def)
      thus "\<epsilon> * indicator {x \<in> A. \<epsilon> \<le> f x} x \<le> max 0 (f x)" by (simp add: indicator_def)
    qed
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
  apply (rule integral_count_space_countable[where A=UNIV and f="Rep_distr \<mu>", simplified])
proof -
  have "\<And>x\<^sub>1. (\<forall>R. 0 \<le> ereal (Rep_distr x\<^sub>1 R)) \<and> (\<integral>\<^sup>+ R. ereal (Rep_distr x\<^sub>1 R) \<partial>count_space UNIV) \<le> 1" using Rep_distr by auto
  thus "(\<integral>\<^sup>+ x. ereal (Rep_distr \<mu> x) \<partial>count_space UNIV) \<noteq> \<infinity>" by (metis (no_types) ereal_infty_less_eq(1) ereal_times(1))
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
      using `y \<in> Y` domY by blast
    with domX have f0: "\<And>x. x\<in>X \<Longrightarrow> f x y = 0"
      using `y \<in> Y` by blast
    show ?thesis apply (subst indicator_simps(2)) using False close simp
    apply auto using f0 by (subst nn_integral_0_iff_AE, auto)
  qed}
  hence "?left = (\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f x y \<partial>count_space X) * indicator ?Y y \<partial>count_space Y)"
    by (rule_tac nn_integral_cong, auto)
  also have "... = (\<integral>\<^sup>+ y. (\<integral>\<^sup>+ x. f x y \<partial>count_space X) \<partial>count_space ?Y)"
      apply (subst nn_integral_restrict_space[symmetric]) close auto
      unfolding restrict_count_space 
      by (tactic "cong_tac @{context} 1", auto)+
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
    by (tactic "cong_tac @{context} 1", auto)+
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
    by (tactic "cong_tac @{context} 1", auto)+
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
    by (tactic "cong_tac @{context} 1", auto)+
  also have "\<dots> = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. f x y \<partial>count_space Y) \<partial>count_space X)" 
    apply (rule_tac nn_integral_cong, auto)
    by (simp add: aux indicator_def nn_integral_nonneg)
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
lemma ereal_Rep_compose_distr: "ereal (Rep_distr (compose_distr f \<mu>) b) =
  (\<integral>\<^sup>+a. Rep_distr \<mu> a * Rep_distr (f a) b \<partial>count_space UNIV)"
proof -
  have aux1: "\<And>a b::ereal. a\<ge>0 \<Longrightarrow> b\<le>1 \<Longrightarrow> a*b \<le> a"
    by (metis ereal_mult_right_mono monoid_mult_class.mult.left_neutral mult.commute) 
  have nn_integral_counting_single_aux: "\<And>x X f. x\<in>X \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>count_space X) < \<infinity> \<Longrightarrow> f x < \<infinity>"
    by (metis ereal_infty_less(1) nn_integral_counting_single not_less)
    
  have "(\<integral>\<^sup>+ b. \<integral>\<^sup>+ a. ereal (Rep_distr \<mu> a * Rep_distr (f a) b)
            \<partial>count_space UNIV \<partial>count_space UNIV) =
        (\<integral>\<^sup>+ a. \<integral>\<^sup>+ b. ereal (Rep_distr \<mu> a * Rep_distr (f a) b)
            \<partial>count_space UNIV \<partial>count_space UNIV)" (is "?int_ba = ?int_ab")
    by (rule Fubini_count_space)
  also have "... = (\<integral>\<^sup>+ a. ereal (Rep_distr \<mu> a) * \<integral>\<^sup>+ b. ereal (Rep_distr (f a) b)
            \<partial>count_space UNIV \<partial>count_space UNIV)"
    by (subst nn_integral_cmult[symmetric], auto simp: Rep_distr_geq0)
  also have "... \<le> (\<integral>\<^sup>+ a. ereal (Rep_distr \<mu> a) \<partial>count_space UNIV)"
    apply (rule nn_integral_mono, auto, rule aux1)
    close (metis Rep_distr_geq0 ereal_less_eq(5))
    using Rep_distr by auto
  also have "\<dots> \<le> 1"
    using Rep_distr by auto
  finally have "?int_ba \<le> 1" by simp
  with `?int_ba = ?int_ab` have "?int_ab \<le> 1" by simp
  have int_b:"\<And>a. (\<integral>\<^sup>+ b. ereal (Rep_distr \<mu> b * Rep_distr (f b) a) \<partial>count_space UNIV) < \<infinity>"
    apply (rule_tac x=a and X=UNIV in nn_integral_counting_single_aux, auto)
    using `?int_ba \<le> 1`
    by (metis PInfty_neq_ereal(1) ereal_infty_less_eq(1) one_ereal_def)
  show ?thesis
    unfolding compose_distr_def apply (subst Abs_distr_inverse, auto)
      close (metis nn_integral_nonneg real_of_ereal_pos)
     apply (subst ereal_real')
      using int_b close auto
     using `?int_ba \<le> 1` close assumption
    using ereal_real int_b by auto
qed
lemma Rep_compose_distr: "Rep_distr (compose_distr f \<mu>) b =
  real (\<integral>\<^sup>+a. Rep_distr \<mu> a * Rep_distr (f a) b \<partial>count_space UNIV)"
  by (subst ereal_Rep_compose_distr[symmetric], simp)

(* proof -
  have aux1: "\<And>a b::ereal. a\<ge>0 \<Longrightarrow> b\<le>1 \<Longrightarrow> a*b \<le> a"
    by (metis ereal_mult_right_mono monoid_mult_class.mult.left_neutral mult.commute) 
  have nn_integral_counting_single_aux: "\<And>x X f. x\<in>X \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>count_space X) < \<infinity> \<Longrightarrow> f x < \<infinity>"
    by (metis ereal_infty_less(1) nn_integral_counting_single not_less)
    
  have "(\<integral>\<^sup>+ b. \<integral>\<^sup>+ a. ereal (Rep_distr \<mu> a * Rep_distr (f a) b)
            \<partial>count_space UNIV \<partial>count_space UNIV) =
        (\<integral>\<^sup>+ a. \<integral>\<^sup>+ b. ereal (Rep_distr \<mu> a * Rep_distr (f a) b)
            \<partial>count_space UNIV \<partial>count_space UNIV)" (is "?int_ba = ?int_ab")
    by (rule Fubini_count_space)
  also have "... = (\<integral>\<^sup>+ a. ereal (Rep_distr \<mu> a) * \<integral>\<^sup>+ b. ereal (Rep_distr (f a) b)
            \<partial>count_space UNIV \<partial>count_space UNIV)"
    by (subst nn_integral_cmult[symmetric], auto simp: Rep_distr_geq0)
  also have "... \<le> (\<integral>\<^sup>+ a. ereal (Rep_distr \<mu> a) \<partial>count_space UNIV)"
    apply (rule nn_integral_mono, auto, rule aux1)
    close (metis Rep_distr_geq0 ereal_less_eq(5))
    using Rep_distr by auto
  also have "\<dots> \<le> 1"
    using Rep_distr by auto
  finally have "?int_ba \<le> 1" by simp
  with `?int_ba = ?int_ab` have "?int_ab \<le> 1" by simp
  have int_b:"\<And>a. (\<integral>\<^sup>+ b. ereal (Rep_distr \<mu> b * Rep_distr (f b) a) \<partial>count_space UNIV) < \<infinity>"
    apply (rule_tac x=a and X=UNIV in nn_integral_counting_single_aux, auto)
    using `?int_ba \<le> 1`
    by (metis PInfty_neq_ereal(1) ereal_infty_less_eq(1) one_ereal_def)
  show ?thesis
    unfolding compose_distr_def apply (subst Abs_distr_inverse, auto)
     close (metis nn_integral_nonneg real_of_ereal_pos)
    apply (subst ereal_real')
     using int_b close auto
    using `?int_ba \<le> 1` .
qed *)

definition apply_to_distr :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" where
  "apply_to_distr f \<mu> = Abs_distr (\<lambda>b. real (\<integral>\<^sup>+a. Rep_distr \<mu> a * indicator {f a} b \<partial>count_space UNIV))"
lemma Rep_apply_to_distr [simp]: "Rep_distr (apply_to_distr f \<mu>)
  = (\<lambda>b. real (\<integral>\<^sup>+a. Rep_distr \<mu> a * indicator {f a} b \<partial>count_space UNIV))"
proof -
  def d == "\<lambda>x. ereal (Rep_distr \<mu> x)"
  have dpos: "\<And>x. d x \<ge> 0" and d_int: "(\<integral>\<^sup>+ y. d y \<partial>count_space UNIV) \<le> 1" 
    unfolding d_def using Rep_distr Rep_distr_geq0 by auto
  have "\<And>x. (\<integral>\<^sup>+ xa. d xa * indicator {f xa} x \<partial>count_space UNIV) \<le> (\<integral>\<^sup>+ y. d y \<partial>count_space UNIV)"
    apply (rule nn_integral_mono)
    by (simp add: dpos indicator_def)
  also note d_int
  also have "(1::ereal) < \<infinity>" by auto
  finally have finite: "\<And>x. (\<integral>\<^sup>+ xa. d xa * indicator {f xa} x \<partial>count_space UNIV) < \<infinity>" by assumption
  have leq1: "(\<integral>\<^sup>+ x. (\<integral>\<^sup>+ xa. (d xa * indicator {f xa} x) \<partial>count_space UNIV) \<partial>count_space UNIV) \<le> 1"
    apply (subst Fubini_count_space)
    apply (subst nn_integral_cmult_indicator)
      close (fact dpos)
     close simp
    using d_int by (auto simp: one_ereal_def[symmetric])
  hence leq1': "(\<integral>\<^sup>+ x. ereal (real (\<integral>\<^sup>+ xa. (d xa * indicator {f xa} x) \<partial>count_space UNIV)) \<partial>count_space UNIV) \<le> 1"
    apply (subst ereal_real') using finite by auto
  show ?thesis
    unfolding apply_to_distr_def
    apply (rule Abs_distr_inverse, auto)
    using nn_integral_nonneg real_of_ereal_pos close blast
    apply (subst times_ereal.simps(1)[symmetric], simp)
    using leq1' unfolding d_def
    by (metis (no_types, lifting) ereal_mult_indicator nn_integral_cong) 
qed

lemma compose_point_distr_r [simp]: "compose_distr f (point_distr x) = f x"
proof -
  have rw: "\<And>y b. ereal ((if y = x then 1 else 0) * Rep_distr (f y) b) =
                  ereal (Rep_distr (f x) b) * indicator {x} y"
    by simp
  show ?thesis
    unfolding compose_distr_def 
    apply simp unfolding rw
    apply (subst nn_integral_cmult_indicator)
    close (simp add: Rep_distr_geq0)
    close simp
    by (simp add: Rep_distr_inverse)
qed

lemma compose_point_distr_l [simp]: "compose_distr (\<lambda>x. point_distr (f x)) \<mu> = apply_to_distr f \<mu>"
  unfolding compose_distr_def point_distr_def apply_to_distr_def
  apply (subst Abs_distr_inverse, auto)
  by (subst ereal_indicator, auto)

lemma apply_to_distr_id [simp]: "apply_to_distr (\<lambda>x. x) \<mu> = \<mu>"
proof -
  have rew1: "\<And>x b. ereal (Rep_distr \<mu> x) * indicator {x} b = ereal (Rep_distr \<mu> b) * indicator {b} x"
    by (case_tac "x=b", auto)
  show ?thesis
    unfolding apply_to_distr_def compose_distr_def Rep_point_distr
    unfolding ereal_mult_indicator rew1 
    apply (subst nn_integral_cmult_indicator, auto simp: Rep_distr_geq0)
    by (rule Rep_distr_inverse)
qed


lemma support_point_distr [simp]: "support_distr (point_distr x) = {x}"
  unfolding support_distr_def by simp

lemma support_compose_distr [simp]: "support_distr (compose_distr f g) = (\<Union>x\<in>support_distr g. support_distr (f x))"
proof -
  have "\<And>x. x \<in> support_distr (compose_distr f g) \<Longrightarrow> x \<in> (\<Union>x\<in>support_distr g. support_distr (f x))"
  proof -
    fix x assume "x \<in> support_distr (compose_distr f g)"
    hence "Rep_distr (compose_distr f g) x > 0" unfolding support_distr_def by simp
    hence "(\<integral>\<^sup>+ y. ereal (Rep_distr g y * Rep_distr (f y) x) \<partial>count_space UNIV) > 0" 
      unfolding Rep_compose_distr using zero_less_real_of_ereal by auto
    then obtain y where x: "ereal (Rep_distr g y * Rep_distr (f y) x) > 0" apply atomize_elim by (rule nn_integral_pos)
    hence "Rep_distr g y > 0" and "Rep_distr (f y) x > 0"
      apply auto using Rep_distr_geq0 less_eq_real_def by fastforce+
    hence "y \<in> support_distr g" and "x \<in> support_distr (f y)"
      by (simp_all add: support_distr_def)
    thus "x \<in> (\<Union>y\<in>support_distr g. support_distr (f y))" by auto
  qed
  moreover have "\<And>x. x \<in> (\<Union>x\<in>support_distr g. support_distr (f x)) \<Longrightarrow> x \<in> support_distr (compose_distr f g)"
  proof -
    let ?fg = "\<lambda>y x. ereal (Rep_distr g y * Rep_distr (f y) x)" 
    fix x assume "x \<in> (\<Union>x\<in>support_distr g. support_distr (f x))"
    then obtain y where "y \<in> support_distr g" and "x \<in> support_distr (f y)" by blast
    hence "Rep_distr g y > 0" and "Rep_distr (f y) x > 0" unfolding support_distr_def by auto
    hence "?fg y x > 0" by auto
    also have "(\<integral>\<^sup>+ y. ?fg y x \<partial>count_space UNIV) \<ge> ?fg y x"
      by (rule nn_integral_ge_point, simp)
    finally have "ereal (Rep_distr (compose_distr f g) x) > 0"
      unfolding ereal_Rep_compose_distr by simp
    thus "x \<in> support_distr (compose_distr f g)"
      by (simp add: support_distr_def)
  qed
  ultimately show ?thesis by auto
qed

lemma support_apply_to_distr [simp]: "support_distr (apply_to_distr f \<mu>) = f ` support_distr \<mu>"
  apply (subst compose_point_distr_l[symmetric])
  apply (subst support_compose_distr)
  by auto

definition "product_distr \<mu> \<nu> = Abs_distr (\<lambda>(x,y). Rep_distr \<mu> x * Rep_distr \<nu> y)"
lemma product_Rep_distr [simp]: "Rep_distr (product_distr \<mu> \<nu>) (x,y) = Rep_distr \<mu> x * Rep_distr \<nu> y"
proof -
  have pos: "\<And>a b. Rep_distr \<mu> a * Rep_distr \<nu> b \<ge> 0"
    by (simp add: Rep_distr_geq0)
  have leq1\<mu>: "(\<integral>\<^sup>+ x. ereal (Rep_distr \<mu> x) \<partial>count_space UNIV) \<le> 1"
    by (rule Rep_distr_int_leq1)
  have leq1\<nu>: "(\<integral>\<^sup>+ x. ereal (Rep_distr \<nu> x) \<partial>count_space UNIV) \<le> 1"
    by (rule Rep_distr_int_leq1)
  have "(\<integral>\<^sup>+ xy. ereal (case xy of (x, y) \<Rightarrow> Rep_distr \<mu> x * Rep_distr \<nu> y) \<partial>count_space UNIV)
       \<le> (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. ereal (Rep_distr \<mu> x) * ereal (Rep_distr \<nu> y) \<partial>count_space UNIV \<partial>count_space UNIV)"
    by (subst nn_integral_fst_count_space[symmetric], simp)
  also have "\<dots> = (\<integral>\<^sup>+ x. ereal (Rep_distr \<mu> x) * \<integral>\<^sup>+ y. ereal (Rep_distr \<nu> y) \<partial>count_space UNIV \<partial>count_space UNIV)"
    apply (subst nn_integral_cmult) by (simp_all add: Rep_distr_geq0)
  also have "\<dots> = (\<integral>\<^sup>+ x. ereal (Rep_distr \<mu> x) \<partial>count_space UNIV) * (\<integral>\<^sup>+ y. ereal (Rep_distr \<nu> y) \<partial>count_space UNIV)"
    apply (subst nn_integral_multc) by (simp_all add: nn_integral_nonneg)
  also with leq1\<mu> leq1\<nu> have "\<dots> \<le> 1 * 1"
    using dual_order.trans ereal_mult_left_mono nn_integral_nonneg by fastforce 
  finally have eq: "(\<integral>\<^sup>+ x. ereal (case x of (x, y) \<Rightarrow> Rep_distr \<mu> x * Rep_distr \<nu> y) \<partial>count_space UNIV) \<le> 1"
    by simp
  show ?thesis
    unfolding product_distr_def
    apply (subst Abs_distr_inverse)
    using pos eq by auto
qed
lemma fst_product_distr [simp]: "apply_to_distr fst (product_distr \<mu> \<nu>) = weight_distr \<nu> *\<^sub>R \<mu>"
proof (subst Rep_distr_inject[symmetric], rule ext)
  fix x0
  have tmp1: "\<And>x y. Rep_distr (product_distr \<mu> \<nu>) (x,y) * indicator {x} x0 = Rep_distr (product_distr \<mu> \<nu>) (x0,y) * indicator {x} x0"
    by (metis indicator_simps(2) mult_cancel_right singletonD)

  have "(\<integral>\<^sup>+ x. indicator {x} x0 \<partial>count_space UNIV) = (\<integral>\<^sup>+ x. indicator {x0} x \<partial>count_space UNIV)"
    by (metis indicator_def singletonD)
  also have "\<dots> = 1" apply (subst nn_integral_indicator) by auto
  finally have tmp2: "(\<integral>\<^sup>+ x. indicator {x} x0 \<partial>count_space UNIV) = 1" by assumption

  have "Rep_distr (apply_to_distr fst (product_distr \<mu> \<nu>)) x0
      = real (\<integral>\<^sup>+ xy. ereal (Rep_distr (product_distr \<mu> \<nu>) xy * indicator {fst xy} x0) \<partial>count_space UNIV)"
    by simp
  also have "\<dots> = real (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. (Rep_distr (product_distr \<mu> \<nu>) (x,y) * indicator {x} x0) \<partial>count_space UNIV \<partial>count_space UNIV)"
    by (subst nn_integral_fst_count_space[symmetric], simp)
  also have "\<dots> = real (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. (Rep_distr (product_distr \<mu> \<nu>) (x0,y)) \<partial>count_space UNIV) * indicator {x} x0 \<partial>count_space UNIV)"
    unfolding times_ereal.simps(1)[symmetric] tmp1
    apply (subst nn_integral_multc) apply (simp_all add: Rep_distr_geq0)
    by (metis ereal_indicator)
  also have "\<dots> = real ((\<integral>\<^sup>+ y. (Rep_distr (product_distr \<mu> \<nu>) (x0,y)) \<partial>count_space UNIV) * (\<integral>\<^sup>+ x. indicator {x} x0 \<partial>count_space UNIV))"
    apply (subst nn_integral_cmult) by (simp_all add: nn_integral_nonneg)
  also have "\<dots> = real (\<integral>\<^sup>+ y. (Rep_distr (product_distr \<mu> \<nu>) (x0,y)) \<partial>count_space UNIV)"
    using tmp2 by simp
  also have "\<dots> = real (\<integral>\<^sup>+ x. ereal (Rep_distr \<mu> x0 * Rep_distr \<nu> x) \<partial>count_space UNIV)"
    by simp    
  also have "\<dots> = real (ereal (Rep_distr \<mu> x0) * \<integral>\<^sup>+ x. ereal (Rep_distr \<nu> x) \<partial>count_space UNIV)"
    unfolding times_ereal.simps(1)[symmetric]
    by (subst nn_integral_cmult, auto intro: Rep_distr_geq0)
  also have "\<dots> = weight_distr \<nu> * Rep_distr \<mu> x0"
    unfolding weight_distr_def by auto
  also have "\<dots> = Rep_distr (weight_distr \<nu> *\<^sub>R \<mu>) x0"
    apply (subst Rep_distr_scaleR) using weight_distr_pos  weight_distr_leq1 by auto
  finally show "Rep_distr (apply_to_distr fst (product_distr \<mu> \<nu>)) x0 = Rep_distr (weight_distr \<nu> *\<^sub>R \<mu>) x0"
    by assumption
qed

lemma snd_product_distr [simp]: "apply_to_distr snd (product_distr \<mu> \<nu>) = weight_distr \<mu> *\<^sub>R \<nu>"
  SORRY

lemma support_product_distr [simp]: "support_distr (product_distr \<mu> \<nu>) = support_distr \<mu> \<times> support_distr \<nu>"
  unfolding support_distr_def
  apply auto unfolding product_Rep_distr
  close (metis Rep_distr_geq0 less_eq_real_def mult_zero_left)
  close (metis Rep_distr_geq0 less_eq_real_def mult_zero_right)
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
  show "apply_to_distr (\<lambda>(x,y,z). (x,y)) \<mu> = \<mu>1" SORRY "distribution laws"
  show "apply_to_distr (\<lambda>(x,y,z). (y,z)) \<mu> = \<mu>2" SORRY "distribution laws"
qed


lemma compose_distr_assoc: "compose_distr (\<lambda>x. compose_distr g (f x)) \<mu> = compose_distr g (compose_distr f \<mu>)" 
  SORRY

(*
subsection {* Combining ell1 and distr *}

definition "distr_to_ell1 \<mu> = Abs_ell1 (Rep_distr \<mu>)"
definition "ell1_to_distr \<mu> = Abs_distr (Rep_ell1 \<mu>)"

lemma distr_to_ell1_apply_comm [simp]: "distr_to_ell1 (apply_to_distr f \<mu>) = apply_to_ell1 f (distr_to_ell1 \<mu>)"
  SORRY
lemma support_distr_to_ell1 [simp]: "support_ell1 (distr_to_ell1 \<mu>) = support_distr \<mu>"
  SORRY
*)

lemma compose_distr_cong: 
  fixes f1 f2 \<mu>
  assumes "\<And>x. x\<in>support_distr \<mu> \<Longrightarrow> f1 x = f2 x"
  shows "compose_distr f1 \<mu> = compose_distr f2 \<mu>"
SORRY

lemma apply_to_distr_cong: 
  fixes f1 f2 \<mu>
  assumes "\<And>x. x\<in>support_distr \<mu> \<Longrightarrow> f1 x = f2 x"
  shows "apply_to_distr f1 \<mu> = apply_to_distr f2 \<mu>"
SORRY

lemma compose_distr_apply_to_distr: 
  shows "compose_distr f (apply_to_distr g \<mu>) = compose_distr (f o g) \<mu>"
proof -
  have "compose_distr (\<lambda>c. compose_distr f (point_distr (g c))) \<mu> = compose_distr (f \<circ> g) \<mu>"
    by (metis (no_types) comp_def compose_point_distr_r)
  thus ?thesis
    by (metis compose_distr_assoc compose_point_distr_l)
qed

lemma apply_to_distr_twice [simp]: "apply_to_distr f (apply_to_distr g \<mu>) = apply_to_distr (\<lambda>x. f (g x)) \<mu>"
  apply (subst compose_point_distr_l[symmetric])
  apply (subst compose_distr_apply_to_distr)
  unfolding o_def 
  apply (subst compose_point_distr_l) by simp


lemma Rep_distr_0 [simp]: "Rep_distr 0 = (\<lambda>x. 0)"
  unfolding zero_distr_def apply (subst Abs_distr_inverse) apply auto
  by (metis ereal_zero_times zero_ereal_def zero_less_one_ereal)

lemma apply_to_distr_0 [simp]: "apply_to_distr f 0 = 0"
  unfolding apply_to_distr_def apply simp
  unfolding zero_distr_def by auto

lemma apply_to_distr_compose_distr:
  shows "apply_to_distr f (compose_distr g h) = compose_distr (\<lambda>m. apply_to_distr f (g m)) h"
  by (metis (no_types, lifting) compose_distr_assoc compose_distr_cong compose_point_distr_l)


end
