theory Distr
imports Main Tools "~~/src/HOL/Probability/Binary_Product_Measure" Misc
begin

lemma indicator_singleton: "indicator {x} y = indicator {y} x"
  unfolding indicator_def by auto

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
definition "ereal_Rep_distr a m = ereal (Rep_distr a m)"
definition "ereal_Abs_distr a = Abs_distr (\<lambda>m. real (a m))"
lemma real_ereal_Rep_distr: "real (ereal_Rep_distr a m) = Rep_distr a m"
  unfolding ereal_Rep_distr_def by simp
lemma ereal_Rep_distr: "ereal (Rep_distr a m) = ereal_Rep_distr a m"
  unfolding ereal_Rep_distr_def by simp
lemma ereal_Abs_distr_inverse: 
  assumes pos: "\<And>x. a x \<ge> 0"
  assumes leq1: "(\<integral>\<^sup>+ x. a x \<partial>count_space UNIV) \<le> 1"
  shows "ereal_Rep_distr (ereal_Abs_distr a) = a"
proof -
  {fix m
  have rpos: "\<And>x. real (a x) \<ge> 0"
    using pos real_of_ereal_pos by blast
  from leq1 have aleq1: "\<And>x. a x \<le> 1"
    by (meson UNIV_I dual_order.trans nn_integral_ge_point)
  hence a_real: "\<And>x. ereal (real (a x)) = a x"
    by (metis abs_ereal_ge0 antisym ereal_real' ereal_times(1) pos top_ereal_def top_greatest)
  have "ereal_Rep_distr (ereal_Abs_distr a) m = a m"
    unfolding ereal_Rep_distr_def ereal_Abs_distr_def
    apply (subst Abs_distr_inverse)
    using rpos a_real leq1 by auto}
  thus ?thesis by auto
qed

lemma ereal_Abs_distr_inverse': 
  assumes pos: "\<And>x. a x \<ge> 0"
  assumes leq1: "(\<integral>\<^sup>+ x. ereal (a x) \<partial>count_space UNIV) \<le> 1"
  shows "ereal_Rep_distr (Abs_distr a) = (\<lambda>m. ereal (a m))"
proof -
  have "ereal_Rep_distr (Abs_distr a) = ereal_Rep_distr (ereal_Abs_distr (\<lambda>m. ereal (a m)))"
    unfolding ereal_Abs_distr_def by auto                                                                               
  also have "\<dots> = (\<lambda>m. ereal (a m))"
    apply (rule ereal_Abs_distr_inverse)
    using pos close auto
    using leq1 by auto
  finally show ?thesis by assumption
qed

lemma ereal_Rep_distr_inverse: "ereal_Abs_distr (ereal_Rep_distr a) = a"
  unfolding ereal_Abs_distr_def ereal_Rep_distr_def apply simp
  by (fact Rep_distr_inverse)

lemma ereal_Rep_distr_inject: "(ereal_Rep_distr x = ereal_Rep_distr y) = (x = y)"
  using ereal_Rep_distr_inverse by metis

lemma Rep_distr_geq0 [simp]: "Rep_distr \<mu> x \<ge> 0"
  using Rep_distr[of \<mu>] by auto 
lemma ereal_Rep_distr_geq0 [simp]: "ereal_Rep_distr \<mu> x \<ge> 0"
  unfolding ereal_Rep_distr_def apply (subst ereal_less_eq(5)) by (rule Rep_distr_geq0)
lemma ereal_Rep_distr_not_inf [simp]: "ereal_Rep_distr \<mu> x \<noteq> \<infinity>"
  by (simp add: ereal_Rep_distr_def)

lemma ereal_Rep_distr_int_leq1: "(\<integral>\<^sup>+x. ereal_Rep_distr \<mu> x \<partial>count_space UNIV) \<le> 1"
  unfolding ereal_Rep_distr_def using Rep_distr[of \<mu>] by auto
lemma ereal_Rep_distr_leq1 [simp]: "ereal_Rep_distr \<mu> x \<le> 1"
  by (meson UNIV_I ereal_Rep_distr_int_leq1 le_less_trans nn_integral_ge_point not_le)
lemma Rep_distr_leq1 [simp]: "Rep_distr \<mu> x \<le> 1"
  unfolding ereal_less_eq(3)[symmetric] ereal_Rep_distr one_ereal_def[symmetric]
  by (rule ereal_Rep_distr_leq1)

instantiation distr :: (type) zero begin
definition zero_distr :: "'a distr" where "zero_distr = Abs_distr (\<lambda>x. 0)"
instance ..
end
lemma Rep_distr_0 [simp]: "Rep_distr 0 = (\<lambda>x. 0)"
  unfolding zero_distr_def apply (subst Abs_distr_inverse) apply auto
  by (metis ereal_zero_times zero_ereal_def zero_less_one_ereal)
lemma ereal_Rep_distr_0 [simp]: "ereal_Rep_distr 0 = (\<lambda>x. 0)"
  unfolding ereal_Rep_distr_def[THEN ext] by auto

definition support_distr :: "'a distr \<Rightarrow> 'a set" where
  "support_distr \<mu> = {x. Rep_distr \<mu> x > 0}"
lemma support_distr_def': "support_distr \<mu> = {x. ereal_Rep_distr \<mu> x > 0}"
  unfolding support_distr_def ereal_Rep_distr_def by auto
lemma support_distr_def'': "support_distr \<mu> = {x. ereal_Rep_distr \<mu> x \<noteq> 0}"
  unfolding support_distr_def' using ereal_Rep_distr_geq0 less_eq_ereal_def by fastforce 
lemma support_distr_0 [simp]: "support_distr 0 = {}"
  unfolding support_distr_def Rep_distr_0 by simp 

definition "ereal_probability \<mu> E = (\<integral>\<^sup>+x. ereal_Rep_distr \<mu> x * indicator E x \<partial>count_space UNIV)" 
definition "probability \<mu> E = real (\<integral>\<^sup>+x. ereal_Rep_distr \<mu> x * indicator E x \<partial>count_space UNIV)" 
lemma probability_singleton [simp]: "probability \<mu> {x} = Rep_distr \<mu> x"
  unfolding probability_def times_ereal.simps(1)[symmetric] ereal_indicator
  apply (subst nn_integral_singleton_indicator_countspace) by (auto simp: real_ereal_Rep_distr)
lemma ereal_probability: "ereal (probability \<mu> E) = ereal_probability \<mu> E"
proof -
  have "(\<integral>\<^sup>+ x. ereal_Rep_distr \<mu> x * indicator E x \<partial>count_space UNIV) \<le> 
        (\<integral>\<^sup>+ x. ereal_Rep_distr \<mu> x \<partial>count_space UNIV)"
    apply (rule nn_integral_mono, thin_tac _)
    by (simp add: indicator_def)
  also have "\<dots> \<le> 1"
    by (simp add: ereal_Rep_distr_int_leq1)
  also note leq1 = calculation
  show ?thesis
    unfolding probability_def ereal_probability_def apply (subst ereal_real')
    using calculation by auto
qed

abbreviation "weight_distr \<mu> == probability \<mu> UNIV"
lemma ereal_probability_pos [simp]: "ereal_probability \<mu> E \<ge> 0"
  unfolding ereal_probability_def by (simp add: nn_integral_nonneg)
lemma probability_pos [simp]: "probability \<mu> E \<ge> 0"
  apply (subst ereal_less_eq(3)[symmetric])
  apply (subst ereal_probability)
  by (simp add: zero_ereal_def[symmetric])

lemma ereal_probability_leq1 [simp]: "ereal_probability \<mu> E \<le> 1"
proof -
  have "ereal_probability \<mu> E \<le> (\<integral>\<^sup>+ x. ereal (Rep_distr \<mu> x) \<partial>count_space UNIV)"
    unfolding ereal_probability_def
    apply (rule nn_integral_mono, thin_tac _)
    by (metis eq_iff ereal_Rep_distr_def ereal_Rep_distr_geq0 ereal_mult_zero indicator_def mult.right_neutral)
  also have "\<dots> \<le> 1"
    by (simp add: ereal_Rep_distr_int_leq1 ereal_Rep_distr)
  finally show ?thesis by assumption
qed

lemma probability_leq1 [simp]: "probability \<mu> E \<le> 1"
  apply (subst ereal_less_eq(3)[symmetric]) apply (subst ereal_probability)
  unfolding one_ereal_def[symmetric] by simp

instantiation distr :: (type) scaleR begin
definition "scaleR_distr r \<mu> = Abs_distr (\<lambda>x. r * Rep_distr \<mu> x)"
instance ..
end

lemma Rep_distr_scaleR: "r \<ge> 0 \<Longrightarrow> r \<le> 1 \<Longrightarrow> ereal_Rep_distr (r *\<^sub>R \<mu>) x = ereal r * ereal_Rep_distr \<mu> x"
proof -
  assume rpos: "r \<ge> 0" and rleq1: "r \<le> 1"
  have pos: "\<And>x. 0 \<le> r * Rep_distr \<mu> x"
    by (simp add: rpos)
  have "(\<integral>\<^sup>+ x. ereal r * ereal_Rep_distr \<mu> x \<partial>count_space UNIV) = ereal r * (\<integral>\<^sup>+ x. ereal_Rep_distr \<mu> x \<partial>count_space UNIV)"
    apply (subst nn_integral_cmult)
    using rpos by auto
  also have "\<dots> \<le> ereal r * 1"
    apply (rule ereal_mult_left_mono)
    close (rule ereal_Rep_distr_int_leq1)
    using rpos by auto
  also have "\<dots> \<le> 1"
    using rleq1 by auto
  finally have leq1: "(\<integral>\<^sup>+ x. ereal r * ereal_Rep_distr \<mu> x \<partial>count_space UNIV) \<le> 1" by assumption
  have aux: "ereal (r * Rep_distr \<mu> x) = ereal r * ereal_Rep_distr \<mu> x"
    unfolding ereal_Rep_distr_def by (simp only: times_ereal.simps)
  show ?thesis
    unfolding scaleR_distr_def ereal_Rep_distr_def
    apply (subst Abs_distr_inverse)
    using pos leq1 by (auto simp del: times_ereal.simps simp add: times_ereal.simps(1)[symmetric] ereal_Rep_distr)
qed
lemma scaleR_one_distr [simp]: "1 *\<^sub>R (\<mu>::'a distr) = \<mu>"
  unfolding scaleR_distr_def using Rep_distr_inverse by auto  

instantiation distr :: (type) order begin
definition "(a \<le> b) = (Rep_distr a \<le> Rep_distr b)"
lemma less_eq_distr_def': "(a \<le> b) = (ereal_Rep_distr a \<le> ereal_Rep_distr b)"
  unfolding ereal_Rep_distr_def[THEN ext] le_fun_def less_eq_distr_def[THEN ext, THEN ext] by auto
definition "((a::'a distr) < b) = (a \<le> b \<and> \<not> b \<le> a)"
instance apply intro_classes
proof -
  fix x y z::"'a distr"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_distr_def by simp
  show "x \<le> x" unfolding less_eq_distr_def by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding less_eq_distr_def by simp
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding less_eq_distr_def Rep_distr_inject[symmetric] by simp
qed
end

lemma less_eq_ereal_Abs_distr: 
  fixes a b :: "'a \<Rightarrow> ereal"
  assumes "\<And>x. a x \<ge> 0" and "\<And>x. b x \<ge> 0"
  assumes "(\<integral>\<^sup>+x. a x \<partial>count_space UNIV) \<le> 1" and "(\<integral>\<^sup>+x. b x \<partial>count_space UNIV) \<le> 1"
  shows "(a \<le> b) = (ereal_Abs_distr a \<le> ereal_Abs_distr b)"
unfolding less_eq_distr_def'
apply (subst ereal_Abs_distr_inverse)
  using assms close 2
apply (subst ereal_Abs_distr_inverse)
  using assms close 2
by simp

instantiation distr :: (type) order_bot begin
definition "(bot :: 'a distr) = 0"
instance apply intro_classes
  unfolding less_eq_distr_def bot_distr_def le_fun_def by simp
end


lemma mono_Rep_distr: "mono Rep_distr"
  apply (rule monoI) by (simp add: less_eq_distr_def) 
lemma mono_ereal_Rep_distr: "mono ereal_Rep_distr"
  apply (rule monoI) unfolding ereal_Rep_distr_def[THEN ext] le_fun_def
  apply auto using mono_Rep_distr unfolding mono_def le_fun_def by auto


lemma leq_probability: "a \<le> b \<longleftrightarrow> probability a \<le> probability b"
proof 
  fix a b::"'a distr"
  assume "a \<le> b"
  have leq: "\<And>E. (\<integral>\<^sup>+x. ereal_Rep_distr a x * indicator E x \<partial>count_space UNIV) \<le> (\<integral>\<^sup>+x. ereal_Rep_distr b x * indicator E x \<partial>count_space UNIV)"
    apply (rule nn_integral_mono)
    using `a \<le> b` unfolding less_eq_distr_def
    by (metis (no_types, lifting) eq_iff ereal_Rep_distr_def ereal_left_mult_cong ereal_less_eq(3) indicator_def le_funE mult.right_neutral)
  show "probability a \<le> probability b"
    unfolding le_fun_def 
    apply (subst ereal_less_eq(3)[symmetric])
    apply (subst ereal_probability)+
    unfolding ereal_probability_def
    using leq by simp
next
  fix a b::"'a distr"
  assume pr_leq: "probability a \<le> probability b"
  show "a \<le> b"
    unfolding less_eq_distr_def le_fun_def probability_singleton[symmetric]
    using pr_leq unfolding le_fun_def by (auto simp del: probability_singleton)
qed



instantiation distr :: (type) semilattice_inf begin
definition "inf a b = Abs_distr (inf (Rep_distr a) (Rep_distr b))"
lemma Rep_inf_distr: "Rep_distr (inf a b) = inf (Rep_distr a) (Rep_distr b)"
proof -
  have "(\<integral>\<^sup>+ x. ereal (inf (Rep_distr a x) (Rep_distr b x)) \<partial>count_space UNIV) \<le>
        (\<integral>\<^sup>+ x. ereal (Rep_distr a x) \<partial>count_space UNIV)"
    apply (rule nn_integral_mono) by (simp)
  also have "\<dots> \<le> 1" apply (simp add: ereal_Rep_distr) by (rule ereal_Rep_distr_int_leq1)
  finally show ?thesis
    unfolding inf_distr_def apply (subst Abs_distr_inverse) by auto
qed
instance
proof intro_classes
  fix x y z::"'a distr"
  show "inf x y \<le> x" unfolding less_eq_distr_def Rep_inf_distr by auto
  show "inf x y \<le> y" unfolding less_eq_distr_def Rep_inf_distr by auto
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z" unfolding less_eq_distr_def Rep_inf_distr by auto
qed
end

instantiation distr :: (type) sup begin
definition "sup a b = Abs_distr (sup (Rep_distr a) (Rep_distr b))"
instance ..
end

instantiation distr :: (type) Sup begin
definition "Sup A = (if A={} then 0 else Abs_distr (Sup (Rep_distr ` A)))"
instance .. 
end


lemma ereal_Rep_SUP_distr:
  assumes "incseq f"
  shows "ereal_Rep_distr (SUP i. f i) = (SUP i. ereal_Rep_distr (f i))"
proof -
  {fix m
  have "Sup (ereal_Rep_distr ` range f) \<ge> (\<lambda>m. 0)" 
    apply (rule Sup_upper2[where u="ereal_Rep_distr (f 0)"])
    by (auto simp: le_fun_def)
  hence "Sup (ereal_Rep_distr ` range f) m \<ge> 0"
    by (auto simp: le_fun_def)
  moreover have "Sup (ereal_Rep_distr ` range f) \<le> (\<lambda>m. 1)"
    apply (rule Sup_least) unfolding le_fun_def by auto
  hence "Sup (ereal_Rep_distr ` range f) m \<le> 1"
    by (auto simp: le_fun_def)
  ultimately have "\<bar>SUP a. ereal (Rep_distr (f a) m)\<bar> \<noteq> \<infinity>" 
    unfolding SUP_def ereal_Rep_distr_def[THEN ext, THEN ext] by auto}
  note SUP_finite = this

  {fix m
  have "Sup (ereal_Rep_distr ` range f) \<ge> (\<lambda>m. 0)" 
    apply (rule Sup_upper2[where u="ereal_Rep_distr (f 0)"])
    by (auto simp: le_fun_def)
  hence "Sup (ereal_Rep_distr ` range f) m \<ge> 0"
    by (auto simp: le_fun_def)
  hence "Sup (Rep_distr ` range f) m \<ge> 0"
    unfolding ereal_Rep_distr_def[THEN ext, THEN ext] apply simp 
    apply (subst (asm) ereal_SUP[symmetric])
    apply (rule SUP_finite) by auto}
  note Sup_pos = this

  have inc: "incseq (\<lambda>i. ereal_Rep_distr (f i))"
    apply (rule monoI) using mono_ereal_Rep_distr assms unfolding mono_def by auto

  have ereal_move: "(\<lambda>m. ereal (Sup (Rep_distr ` range f) m)) = Sup (range (\<lambda>i. ereal_Rep_distr (f i)))"
    unfolding ereal_Rep_distr_def[THEN ext]
    apply (subst Sup_fun_def) apply simp
    apply (subst ereal_SUP) using SUP_finite by auto

  have "(\<integral>\<^sup>+ x. ereal (Sup (Rep_distr ` range f) x) \<partial>count_space UNIV)
      = (\<integral>\<^sup>+ x. (SUP i. (ereal_Rep_distr (f i)) x) \<partial>count_space UNIV)"
    unfolding ereal_Rep_distr_def[THEN ext, THEN ext]
    apply (rule nn_integral_cong, thin_tac _)
    apply (subst Sup_fun_def) apply simp
    apply (subst ereal_SUP) using SUP_finite by auto
  also have "\<dots> = (SUP i. \<integral>\<^sup>+ x. ((ereal_Rep_distr (f i)) x) \<partial>count_space UNIV)"
    apply (rule nn_integral_monotone_convergence_SUP)
    using inc by auto    
  also have "\<dots> \<le> 1"
    unfolding SUP_def
    apply (rule Sup_least, auto)
    using ereal_Rep_distr_int_leq1 by assumption
  finally have int_leq_1: "(\<integral>\<^sup>+ x. ereal (Sup (Rep_distr ` range f) x) \<partial>count_space UNIV) \<le> 1" by assumption

  show ?thesis
    unfolding Sup_distr_def SUP_def apply simp
    apply (subst ereal_Abs_distr_inverse')
    using Sup_pos int_leq_1 ereal_move by auto
qed                                                    

definition
  is_Sup :: "'a::ord set \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_Sup A s = ((\<forall>x \<in> A. x \<le> s) \<and> (\<forall>z. (\<forall>x \<in> A. x \<le> z) \<longrightarrow> s \<le> z))"

lemma Rep_SUP_ex:
  fixes f :: "nat \<Rightarrow> 'a distr"
  assumes "incseq f"
  shows "is_Sup (range f) (SUP i. f i)"
proof (unfold is_Sup_def, auto)
  fix x
  have "ereal_Rep_distr (f x) \<le> (SUP x. ereal_Rep_distr (f x))"
    by (meson SUP_upper UNIV_I)
  hence leq: "\<And>m. ereal_Rep_distr (f x) m \<le> (SUP x. ereal_Rep_distr (f x) m)"
    by (simp add: le_fun_def)
  show "f x \<le> (SUP x. f x)"
    apply (subst less_eq_distr_def) apply (subst le_fun_def)
    apply (subst ereal_less_eq(3)[symmetric])
    apply (subst ereal_Rep_distr)+
    apply (subst ereal_Rep_SUP_distr)
    using assms leq by auto
next
  fix z assume "\<forall>x. f x \<le> z"
  hence "(SUP i. ereal_Rep_distr (f i)) \<le> ereal_Rep_distr z"
     by (simp add: SUP_least monoD mono_ereal_Rep_distr)
  hence geq: "\<And>x. (SUP i. ereal_Rep_distr (f i)) x \<le> ereal_Rep_distr z x"
    by (simp add: le_fun_def)
  show "(SUP x. f x) \<le> z"
    apply (subst less_eq_distr_def) apply (subst le_fun_def)
    apply (subst ereal_less_eq(3)[symmetric])
    apply (subst ereal_Rep_distr)+
    apply (subst ereal_Rep_SUP_distr)
    using assms geq by auto
qed


definition point_distr :: "'a \<Rightarrow> 'a distr" where "point_distr a = Abs_distr (indicator {a})"
lemma weight_point_distr [simp]: "weight_distr (point_distr a) = 1"
proof - 
  note[[show_consts]]
  have sum1: "(\<integral>\<^sup>+ x. ereal (indicator {a} x) \<partial>count_space UNIV) = 1"
    unfolding ereal_indicator
    by (subst nn_integral_indicator, auto)
  show ?thesis
    apply (subst ereal.inject[symmetric]) unfolding one_ereal_def[symmetric]
    unfolding ereal_probability ereal_probability_def point_distr_def 
    by (subst ereal_Abs_distr_inverse', auto simp: sum1)
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
  unfolding support_distr_def apply (subst less_ereal.simps(1)[symmetric]) unfolding zero_ereal_def[symmetric] ereal_Rep_distr
  apply (rule integral_count_space_countable[where A=UNIV and f="ereal_Rep_distr \<mu>", simplified])
  using ereal_Rep_distr_int_leq1 ereal_infty_less_eq2(1) ereal_times(1) by blast

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
(* Could be proven easily with nn_integral_fst_count_space, nn_integral_snd_count_space, nn_integral_bij_count_space ? *)
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

(* nn_integral_ge_point *)
(* lemma nn_integral_counting_single:
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
qed *)

definition compose_distr :: "('a \<Rightarrow> 'b distr) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" where
  "compose_distr f \<mu> == Abs_distr (\<lambda>b. real (\<integral>\<^sup>+a. Rep_distr \<mu> a * Rep_distr (f a) b \<partial>count_space UNIV))"
lemma ereal_Rep_compose_distr: "ereal_Rep_distr (compose_distr f \<mu>) b =
  (\<integral>\<^sup>+a. ereal_Rep_distr \<mu> a * ereal_Rep_distr (f a) b \<partial>count_space UNIV)"
proof -
  have aux1: "\<And>a b::ereal. a\<ge>0 \<Longrightarrow> b\<le>1 \<Longrightarrow> a*b \<le> a"
    by (metis ereal_mult_right_mono monoid_mult_class.mult.left_neutral mult.commute) 
  have nn_integral_counting_single_aux: "\<And>x X f. x\<in>X \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>count_space X) < \<infinity> \<Longrightarrow> f x < \<infinity>"
    by (metis ereal_infty_less(1) nn_integral_ge_point not_less)
    
  have "(\<integral>\<^sup>+ b. \<integral>\<^sup>+ a. ereal_Rep_distr \<mu> a * ereal_Rep_distr (f a) b
            \<partial>count_space UNIV \<partial>count_space UNIV) =
        (\<integral>\<^sup>+ a. \<integral>\<^sup>+ b. ereal_Rep_distr \<mu> a * ereal_Rep_distr (f a) b
            \<partial>count_space UNIV \<partial>count_space UNIV)" (is "?int_ba = ?int_ab")
    by (rule Fubini_count_space)
  also have "... = (\<integral>\<^sup>+ a. (ereal_Rep_distr \<mu> a) * \<integral>\<^sup>+ b. (ereal_Rep_distr (f a) b)
            \<partial>count_space UNIV \<partial>count_space UNIV)"
    by (subst nn_integral_cmult[symmetric], auto)
  also have "... \<le> (\<integral>\<^sup>+ a. (ereal_Rep_distr \<mu> a) \<partial>count_space UNIV)"
    apply (rule nn_integral_mono, auto, rule aux1)
    close (metis ereal_Rep_distr_geq0)
    by (simp add: ereal_Rep_distr_int_leq1)
  also have "\<dots> \<le> 1"
    by (simp add: ereal_Rep_distr_int_leq1)
  finally have "?int_ba \<le> 1" by simp
  with `?int_ba = ?int_ab` have "?int_ab \<le> 1" by simp
  have int_b:"\<And>a. (\<integral>\<^sup>+ b. (ereal_Rep_distr \<mu> b * ereal_Rep_distr (f b) a) \<partial>count_space UNIV) < \<infinity>"
    apply (rule_tac x=a and X=UNIV in nn_integral_counting_single_aux, auto)
    using `?int_ba \<le> 1` by simp
  show ?thesis
    unfolding compose_distr_def ereal_Rep_distr_def apply (subst Abs_distr_inverse, auto)
      close (metis nn_integral_nonneg real_of_ereal_pos)
     apply (subst ereal_real')
      using int_b unfolding ereal_Rep_distr_def close auto
     using `?int_ba \<le> 1` unfolding ereal_Rep_distr_def close auto
    using ereal_real int_b unfolding ereal_Rep_distr_def by auto
qed
lemma Rep_compose_distr: "Rep_distr (compose_distr f \<mu>) b =
  real (\<integral>\<^sup>+a. Rep_distr \<mu> a * Rep_distr (f a) b \<partial>count_space UNIV)"
  apply (subst ereal_Rep_compose_distr[symmetric, unfolded ereal_Rep_distr_def, simplified]) by simp

definition apply_to_distr :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" where
  "apply_to_distr f \<mu> = Abs_distr (\<lambda>b. real (\<integral>\<^sup>+a. Rep_distr \<mu> a * indicator {f a} b \<partial>count_space UNIV))"
lemma ereal_Rep_apply_to_distr: "ereal_Rep_distr (apply_to_distr f \<mu>) b
  = (\<integral>\<^sup>+a. ereal_Rep_distr \<mu> a * indicator {f a} b \<partial>count_space UNIV)"
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
    unfolding apply_to_distr_def ereal_Rep_distr_def
    apply (subst Abs_distr_inverse, auto)
      using nn_integral_nonneg real_of_ereal_pos close blast
     (* apply (subst times_ereal.simps(1)[symmetric], simp) *)                                     
     using leq1' unfolding d_def ereal_indicator[symmetric] close simp
    apply (subst ereal_real')
     using finite[of b] unfolding d_def ereal_indicator[symmetric] close auto
    by auto
qed

(* lemma Rep_apply_to_distr: "Rep_distr (apply_to_distr f \<mu>)
  = (\<lambda>b. real (\<integral>\<^sup>+a. Rep_distr \<mu> a * indicator {f a} b \<partial>count_space UNIV))"
 *)

lemma ereal_probability_apply_to_distr: "ereal_probability (apply_to_distr f \<mu>) E = ereal_probability \<mu> (f -` E)"
proof -
  have "\<And>x. (\<integral>\<^sup>+ xa. ereal (Rep_distr \<mu> xa * indicator {f xa} x * indicator E x) \<partial>count_space UNIV)
      \<le> (\<integral>\<^sup>+ xa. ereal (Rep_distr \<mu> xa) \<partial>count_space UNIV)"
    apply (rule nn_integral_mono, auto)
    by (smt Rep_distr_geq0 indicator_simps(1) indicator_simps(2) mult_cancel_left1 mult_nonneg_nonpos mult_nonpos_nonneg)
  also have "\<And>x. \<dots> x \<le> 1"
    by (simp add: ereal_Rep_distr ereal_Rep_distr_int_leq1)
  finally have t2: "\<And>x. \<bar>\<integral>\<^sup>+ xa. ereal (Rep_distr \<mu> xa * indicator {f xa} x * indicator E x) \<partial>count_space UNIV\<bar> \<noteq> \<infinity>"
    using abs_eq_infinity_cases ereal_infty_less_eq2(1) ereal_times(1) nn_integral_not_MInfty by blast
    
(*   have "\<And>x. ereal (real (\<integral>\<^sup>+ xa. ereal (Rep_distr \<mu> xa * indicator {f xa} x) \<partial>count_space UNIV) * indicator E x)
      = ereal (real (\<integral>\<^sup>+ xa. ereal (Rep_distr \<mu> xa * indicator {f xa} x) * ereal (indicator E x) \<partial>count_space UNIV))"
    apply (subst nn_integral_multc)
      close auto close auto
    by auto
  also have "\<And>x. \<dots> x = ereal (real (\<integral>\<^sup>+ xa. ereal (Rep_distr \<mu> xa * indicator {f xa} x * indicator E x) \<partial>count_space UNIV))"
    by auto
  also have "\<And>x. \<dots> x = (\<integral>\<^sup>+ xa. ereal (Rep_distr \<mu> xa * indicator {f xa} x * indicator E x) \<partial>count_space UNIV)"
    find_theorems "ereal (real ?x) = ?x"
    apply (subst ereal_real') using t2 by auto 
  finally have t1: "\<And>x. ereal (real (\<integral>\<^sup>+ xa. ereal (Rep_distr \<mu> xa * indicator {f xa} x) \<partial>count_space UNIV) * indicator E x)
        = (\<integral>\<^sup>+ xa. ereal (Rep_distr \<mu> xa * indicator {f xa} x * indicator E x) \<partial>count_space UNIV)"
    by assumption *)

  have ind: "\<And>x. indicator E (f x) = indicator (f -` E) x"
    by (simp add: indicator_def)

  have "ereal_probability (apply_to_distr f \<mu>) E
      = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ xa. ereal_Rep_distr \<mu> xa * indicator {f xa} x * indicator E x \<partial>count_space UNIV) \<partial>count_space UNIV)"
    unfolding ereal_probability_def
    apply (subst nn_integral_multc) by (auto simp: ereal_Rep_apply_to_distr)
  also have "\<dots> = (\<integral>\<^sup>+ xa. (\<integral>\<^sup>+ x. ereal_Rep_distr \<mu> xa * indicator E x * indicator {f xa} x \<partial>count_space UNIV) \<partial>count_space UNIV)"
    apply (subst Fubini_count_space)
    by (smt ereal_zero_times indicator_def nn_integral_cong)
  also have "\<dots> = (\<integral>\<^sup>+ xa. ereal_Rep_distr \<mu> xa * indicator E (f xa) \<partial>count_space UNIV)"
    apply (subst nn_integral_singleton_indicator_countspace) by auto
  also have "\<dots> = (\<integral>\<^sup>+ xa. ereal_Rep_distr \<mu> xa * indicator (f -` E) xa \<partial>count_space UNIV)"
    unfolding ind by rule
  also have "\<dots> = ereal_probability \<mu> (f -` E)"
    unfolding ereal_probability_def by rule
  finally show ?thesis by assumption
qed


lemma probability_apply_to_distr: "probability (apply_to_distr f \<mu>) E = probability \<mu> (f -` E)"
  apply (subst ereal.inject[symmetric]) unfolding ereal_probability
  by (rule ereal_probability_apply_to_distr)

lemma ereal_probability_cong:
  assumes "\<And>x. x \<in> support_distr \<mu> \<Longrightarrow> x\<in>E \<longleftrightarrow> x\<in>F"
  shows "ereal_probability \<mu> E = ereal_probability \<mu> F"
unfolding ereal_probability_def
apply (rule nn_integral_cong, rename_tac x, case_tac "x\<in>support_distr \<mu>")
 close (simp add: assms indicator_def)
unfolding support_distr_def'' by auto

lemma probability_cong:
  assumes "\<And>x. x \<in> support_distr \<mu> \<Longrightarrow> x\<in>E \<longleftrightarrow> x\<in>F"
  shows "probability \<mu> E = probability \<mu> F"
apply (rule ereal.inject[THEN iffD1]) unfolding ereal_probability
apply (rule ereal_probability_cong) using assms by simp

lemma mono_compose_distr1: "mono (\<lambda>f. compose_distr f \<mu>)"
proof (rule monoI, rename_tac f g)
  fix f g::"'a\<Rightarrow>'b distr" assume "f \<le> g"
  show "compose_distr f \<mu> \<le> compose_distr g \<mu>"
    unfolding less_eq_distr_def' le_fun_def apply auto 
    unfolding ereal_Rep_compose_distr
    apply (rule nn_integral_mono, thin_tac _)
    apply (rule ereal_mult_left_mono)
     using `f \<le> g` unfolding le_fun_def less_eq_distr_def' by auto
qed

lemma mono_apply_to_distr: "mono (apply_to_distr f)"
proof (rule monoI, rename_tac \<mu> \<nu>) 
  fix \<mu> \<nu>::"'a distr" assume "\<mu> \<le> \<nu>"
  hence "probability \<mu> \<le> probability \<nu>"
    by (subst leq_probability[symmetric])
  hence "\<And>x. probability \<mu> (f -` {x}) \<le> probability \<nu> (f -` {x})"
    unfolding le_fun_def by auto
  hence "\<And>x. probability (apply_to_distr f \<mu>) {x} \<le> probability (apply_to_distr f \<nu>) {x}"
    unfolding probability_apply_to_distr by assumption
  hence "\<And>x. Rep_distr (apply_to_distr f \<mu>) x \<le> Rep_distr (apply_to_distr f \<nu>) x"
    unfolding probability_singleton by assumption
  thus "apply_to_distr f \<mu> \<le> apply_to_distr f \<nu>"
    unfolding less_eq_distr_def le_fun_def by rule
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
    close (simp)
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
    apply (subst nn_integral_cmult_indicator, auto)
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
      unfolding ereal_Rep_compose_distr[unfolded ereal_Rep_distr_def, simplified] by simp
    thus "x \<in> support_distr (compose_distr f g)"
      by (simp add: support_distr_def)
  qed
  ultimately show ?thesis by auto
qed

lemma support_apply_to_distr [simp]: "support_distr (apply_to_distr f \<mu>) = f ` support_distr \<mu>"
  apply (subst compose_point_distr_l[symmetric])
  apply (subst support_compose_distr)
  by auto

lemma compose_distr_assoc: "compose_distr (\<lambda>x. compose_distr g (f x)) \<mu> = compose_distr g (compose_distr f \<mu>)" 
proof (subst Rep_distr_inject[symmetric], rule ext, subst ereal.inject[symmetric])
  fix a
  have "ereal (Rep_distr (compose_distr (\<lambda>b. compose_distr g (f b)) \<mu>) a)
      = \<integral>\<^sup>+b. ereal (Rep_distr \<mu> b) * \<integral>\<^sup>+c. ereal (Rep_distr (f b) c * Rep_distr (g c) a) \<partial>count_space UNIV \<partial>count_space UNIV"
    apply (subst ereal_Rep_compose_distr[unfolded ereal_Rep_distr_def, simplified])
    apply (subst times_ereal.simps(1)[symmetric])
    apply (subst ereal_Rep_compose_distr[unfolded ereal_Rep_distr_def, simplified])
    by rule
  also have "\<dots> = \<integral>\<^sup>+b. \<integral>\<^sup>+c. ereal (Rep_distr \<mu> b * Rep_distr (f b) c * Rep_distr (g c) a) \<partial>count_space UNIV \<partial>count_space UNIV"
    apply (subst nn_integral_cmult[symmetric])
    apply (auto intro: Rep_distr_geq0)
    by (metis (no_types, lifting) linordered_field_class.sign_simps(23) nn_integral_cong)
  also have "\<dots> = \<integral>\<^sup>+c. \<integral>\<^sup>+b. ereal (Rep_distr \<mu> b * Rep_distr (f b) c * Rep_distr (g c) a) \<partial>count_space UNIV \<partial>count_space UNIV"
    by (rule Fubini_count_space)
  also have "\<dots> = \<integral>\<^sup>+c. (\<integral>\<^sup>+b. ereal (Rep_distr \<mu> b * Rep_distr (f b) c) \<partial>count_space UNIV) * Rep_distr (g c) a \<partial>count_space UNIV"
    apply (subst nn_integral_multc[symmetric])
    by (auto intro: Rep_distr_geq0)
  also have "\<dots> = ereal (Rep_distr (compose_distr g (compose_distr f \<mu>)) a)"
    apply (subst ereal_Rep_compose_distr[unfolded ereal_Rep_distr_def, simplified])
    apply (subst times_ereal.simps(1)[symmetric], subst ereal_Rep_compose_distr[unfolded ereal_Rep_distr_def, simplified])
    by auto
  finally show "ereal (Rep_distr (compose_distr (\<lambda>x. compose_distr g (f x)) \<mu>) a) = ereal (Rep_distr (compose_distr g (compose_distr f \<mu>)) a)"
    by assumption
qed

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


definition "product_distr \<mu> \<nu> = Abs_distr (\<lambda>(x,y). Rep_distr \<mu> x * Rep_distr \<nu> y)"
lemma Rep_product_distr [simp]: "Rep_distr (product_distr \<mu> \<nu>) (x,y) = Rep_distr \<mu> x * Rep_distr \<nu> y"
proof -
  have pos: "\<And>a b. Rep_distr \<mu> a * Rep_distr \<nu> b \<ge> 0"
    by (simp)
  have leq1\<mu>: "(\<integral>\<^sup>+ x. ereal_Rep_distr \<mu> x \<partial>count_space UNIV) \<le> 1"
    by (rule ereal_Rep_distr_int_leq1)
  have leq1\<nu>: "(\<integral>\<^sup>+ x. ereal_Rep_distr \<nu> x \<partial>count_space UNIV) \<le> 1"
    by (rule ereal_Rep_distr_int_leq1)
  have "(\<integral>\<^sup>+ xy. ereal (case xy of (x, y) \<Rightarrow> Rep_distr \<mu> x * Rep_distr \<nu> y) \<partial>count_space UNIV)
       \<le> (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. ereal (Rep_distr \<mu> x) * ereal (Rep_distr \<nu> y) \<partial>count_space UNIV \<partial>count_space UNIV)"
    by (subst nn_integral_fst_count_space[symmetric], simp)
  also have "\<dots> = (\<integral>\<^sup>+ x. ereal (Rep_distr \<mu> x) * \<integral>\<^sup>+ y. ereal (Rep_distr \<nu> y) \<partial>count_space UNIV \<partial>count_space UNIV)"
    apply (subst nn_integral_cmult) by (simp_all)
  also have "\<dots> = (\<integral>\<^sup>+ x. ereal_Rep_distr \<mu> x \<partial>count_space UNIV) * (\<integral>\<^sup>+ y. ereal_Rep_distr \<nu> y \<partial>count_space UNIV)"
    apply (subst nn_integral_multc) unfolding ereal_Rep_distr by (simp_all add: nn_integral_nonneg)
  also from leq1\<mu> leq1\<nu> have "\<dots> \<le> 1 * 1"
    using dual_order.trans ereal_mult_left_mono nn_integral_nonneg by fastforce
  finally have eq: "(\<integral>\<^sup>+ x. ereal (case x of (x, y) \<Rightarrow> Rep_distr \<mu> x * Rep_distr \<nu> y) \<partial>count_space UNIV) \<le> 1"
    by simp
  show ?thesis
    unfolding product_distr_def
    apply (subst Abs_distr_inverse)
    using pos eq by auto
qed

lemma ereal_Rep_product_distr [simp]: "ereal_Rep_distr (product_distr \<mu> \<nu>) (x,y) = ereal_Rep_distr \<mu> x * ereal_Rep_distr \<nu> y"
  unfolding ereal_Rep_distr_def Rep_product_distr by auto

lemma product_distr_sym: "apply_to_distr (\<lambda>(x,y). (y,x)) (product_distr \<mu> \<nu>) = product_distr \<nu> \<mu>"
proof -
  have tmp: "\<And>x. ((\<lambda>(x, y). (y, x)) -` {x}) = {(\<lambda>(x, y). (y, x)) x}" 
    by (case_tac x, auto)
  show ?thesis
    apply (subst Rep_distr_inject[symmetric], rule ext)
    apply (subst probability_singleton[symmetric])
    apply (subst probability_apply_to_distr)
    apply (subst tmp)
    apply (subst probability_singleton)
    by auto
qed

lemma fst_product_distr [simp]: "apply_to_distr fst (product_distr \<mu> \<nu>) = weight_distr \<nu> *\<^sub>R \<mu>"
proof (subst Rep_distr_inject[symmetric], rule ext)
  fix x0
  have ind_UNIV: "\<And>x. indicator UNIV x = 1" unfolding indicator_def by simp

  have tmp1: "\<And>x y. ereal_Rep_distr (product_distr \<mu> \<nu>) (x,y) * indicator {x} x0 = ereal_Rep_distr (product_distr \<mu> \<nu>) (x0,y) * indicator {x} x0"
    by (metis ereal_left_mult_cong indicator_simps(2) singletonD)

  have "(\<integral>\<^sup>+ x. indicator {x} x0 \<partial>count_space UNIV) = (\<integral>\<^sup>+ x. indicator {x0} x \<partial>count_space UNIV)"
    by (metis indicator_def singletonD)
  also have "\<dots> = 1" apply (subst nn_integral_indicator) by auto
  finally have tmp2: "(\<integral>\<^sup>+ x. indicator {x} x0 \<partial>count_space UNIV) = 1" by assumption

  have "ereal_Rep_distr (apply_to_distr fst (product_distr \<mu> \<nu>)) x0
      = (\<integral>\<^sup>+ xy. ereal_Rep_distr (product_distr \<mu> \<nu>) xy * indicator {fst xy} x0 \<partial>count_space UNIV)"
    by (simp add: ereal_Rep_apply_to_distr)
  also have "\<dots> = (\<integral>\<^sup>+ x. \<integral>\<^sup>+ y. ereal_Rep_distr (product_distr \<mu> \<nu>) (x,y) * indicator {x} x0 \<partial>count_space UNIV \<partial>count_space UNIV)"
    by (subst nn_integral_fst_count_space[symmetric], simp)
  also have "\<dots> = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. (ereal_Rep_distr (product_distr \<mu> \<nu>) (x0,y)) \<partial>count_space UNIV) * indicator {x} x0 \<partial>count_space UNIV)"
    unfolding times_ereal.simps(1)[symmetric] tmp1
    apply (subst nn_integral_multc) by simp_all
  also have "\<dots> = ((\<integral>\<^sup>+ y. (ereal_Rep_distr (product_distr \<mu> \<nu>) (x0,y)) \<partial>count_space UNIV) * (\<integral>\<^sup>+ x. indicator {x} x0 \<partial>count_space UNIV))"
    apply (subst nn_integral_cmult) by (simp_all add: nn_integral_nonneg)
  also have "\<dots> = (\<integral>\<^sup>+ y. (ereal_Rep_distr (product_distr \<mu> \<nu>) (x0,y)) \<partial>count_space UNIV)"
    using tmp2 by simp
  also have "\<dots> = (\<integral>\<^sup>+ x. ereal_Rep_distr \<mu> x0 * ereal_Rep_distr \<nu> x \<partial>count_space UNIV)"
    by simp    
  also have "\<dots> = ereal_Rep_distr \<mu> x0 * \<integral>\<^sup>+ x. ereal_Rep_distr \<nu> x \<partial>count_space UNIV"
    unfolding times_ereal.simps(1)[symmetric]
    by (subst nn_integral_cmult, auto intro: Rep_distr_geq0)
  also have "\<dots> = ereal (weight_distr \<nu> * Rep_distr \<mu> x0)"
    unfolding times_ereal.simps(1)[symmetric]
    unfolding ereal_probability ereal_Rep_distr ereal_probability_def ind_UNIV
    by (auto simp: mult.commute)
  also have "\<dots> = ereal_Rep_distr (weight_distr \<nu> *\<^sub>R \<mu>) x0"
    apply (subst Rep_distr_scaleR)
    using probability_pos probability_leq1 by (auto simp: ereal_probability[symmetric] ereal_Rep_distr_def)

  finally show "Rep_distr (apply_to_distr fst (product_distr \<mu> \<nu>)) x0 = Rep_distr (weight_distr \<nu> *\<^sub>R \<mu>) x0"
    unfolding ereal_Rep_distr_def
    by blast
qed

lemma snd_product_distr [simp]: "apply_to_distr snd (product_distr \<mu> \<nu>) = weight_distr \<mu> *\<^sub>R \<nu>"
proof -
  have aux: "(\<lambda>x. snd (case x of (x, y) \<Rightarrow> (y, x))) = fst"
    unfolding snd_def fst_def by auto

  have "apply_to_distr snd (product_distr \<mu> \<nu>) = apply_to_distr snd (apply_to_distr (\<lambda>(x,y). (y,x)) (product_distr \<nu> \<mu>))"
    unfolding product_distr_sym by rule
  also have "\<dots> = apply_to_distr fst (product_distr \<nu> \<mu>)"
    unfolding apply_to_distr_twice aux by rule
  also have "\<dots> = weight_distr \<mu> *\<^sub>R \<nu>"
    by (rule fst_product_distr)
  finally show ?thesis by assumption
qed

lemma support_product_distr [simp]: "support_distr (product_distr \<mu> \<nu>) = support_distr \<mu> \<times> support_distr \<nu>"
  unfolding support_distr_def
  apply auto unfolding Rep_product_distr
  close (metis Rep_distr_geq0 less_eq_real_def mult_zero_left)
  by (metis Rep_distr_geq0 less_eq_real_def mult_zero_right)


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

definition "markov_chain_combine \<mu>1 \<mu>2 = ereal_Abs_distr (\<lambda>(x,y,z). ereal_Rep_distr \<mu>1 (x,y) * ereal_Rep_distr \<mu>2 (y,z) / ereal_Rep_distr (apply_to_distr snd \<mu>1) y)"

lemma markov_chain_combine_all:
  assumes "apply_to_distr snd \<mu>1 = apply_to_distr fst \<mu>2"
  defines "\<mu> == markov_chain_combine \<mu>1 \<mu>2"
  defines "mid == apply_to_distr snd \<mu>1"
  defines "f == (\<lambda>(x,y,z). ereal_Rep_distr \<mu>1 (x,y) * ereal_Rep_distr \<mu>2 (y,z) / ereal_Rep_distr mid y)"
  shows "apply_to_distr (\<lambda>(x::'a,y::'b,z::'c). (x,y)) \<mu> = \<mu>1" 
    and "apply_to_distr (\<lambda>(x,y,z). (y,z)) \<mu> = \<mu>2"
    and "ereal_Rep_distr (markov_chain_combine \<mu>1 \<mu>2) = f"
proof -
  note ereal_Rep_apply_to_distr[simp add]

  have mid_def2: "mid = apply_to_distr fst \<mu>2" using assms mid_def by simp
  (* def f == "(\<lambda>(x,y,z). ereal_Rep_distr \<mu>1 (x,y) * ereal_Rep_distr \<mu>2 (y,z) / ereal_Rep_distr mid y)" *)
  (* def \<mu> == "markov_chain_combine \<mu>1 \<mu>2" *)
  have \<mu>_def': "\<mu> = ereal_Abs_distr f"
    unfolding \<mu>_def markov_chain_combine_def f_def mid_def by simp
  have f2: "\<And>x y z. f (x,y,z) = (ereal_Rep_distr \<mu>1 (x,y)) * ((1 / ereal_Rep_distr mid y) * (ereal_Rep_distr \<mu>2 (y,z)))"
    unfolding f_def by (simp add: ereal_times_divide_eq)
  have f3: "\<And>x y z. f (x,y,z) = (ereal_Rep_distr \<mu>2 (y,z)) * ((1 / ereal_Rep_distr mid y) * (ereal_Rep_distr \<mu>1 (x,y)))"
    unfolding f_def by (simp add: ereal_times_divide_eq mult.commute)
  
  have mid0: "\<And>y z. ereal_Rep_distr mid y = 0 \<Longrightarrow> ereal_Rep_distr \<mu>2 (y, z) = 0"
  proof -
    fix y0 z0 assume "ereal_Rep_distr mid y0 = 0"
    hence "0 = ereal_Rep_distr mid y0" by simp
    also have "\<dots> = \<integral>\<^sup>+z. \<integral>\<^sup>+y. ereal_Rep_distr \<mu>2 (y,z) * indicator {y} y0 \<partial>count_space UNIV \<partial>count_space UNIV"
      apply (subst mid_def2, simp add: ereal_Rep_distr)
      apply (subst nn_integral_snd_count_space[symmetric])
      by simp
    also have "\<dots> = \<integral>\<^sup>+z. ereal_Rep_distr \<mu>2 (y0,z) \<partial>count_space UNIV"
      unfolding times_ereal.simps(1)[symmetric] ereal_indicator
      apply (subst indicator_singleton)
      apply (subst nn_integral_singleton_indicator_countspace)
      by (auto)
    also have "\<dots> \<ge> ereal_Rep_distr \<mu>2 (y0,z0)"
      by (rule nn_integral_ge_point, simp)
    finally show "ereal_Rep_distr \<mu>2 (y0, z0) = 0"
      unfolding ereal_Rep_distr_def
      by (simp add: eq_iff)
  qed

  have mid0': "\<And>x y. ereal_Rep_distr mid y = 0 \<Longrightarrow> ereal_Rep_distr \<mu>1 (x, y) = 0"
  proof -
    fix x0 y0 assume "ereal_Rep_distr mid y0 = 0"
    hence "0 = ereal_Rep_distr mid y0" by simp
    also have "\<dots> = \<integral>\<^sup>+x. \<integral>\<^sup>+y. ereal_Rep_distr \<mu>1 (x,y) * indicator {y} y0 \<partial>count_space UNIV \<partial>count_space UNIV"
      apply (subst mid_def, simp)
      by (subst nn_integral_fst_count_space[symmetric], simp)
    also have "\<dots> = \<integral>\<^sup>+x. ereal_Rep_distr \<mu>1 (x,y0) \<partial>count_space UNIV"
      unfolding times_ereal.simps(1)[symmetric] ereal_indicator
      apply (subst indicator_singleton)
      apply (subst nn_integral_singleton_indicator_countspace)
      by auto
    also have "\<dots> \<ge> ereal_Rep_distr \<mu>1 (x0,y0)"
      by (rule nn_integral_ge_point, simp)
    finally show "ereal_Rep_distr \<mu>1 (x0,y0) = 0"
      by (simp add: eq_iff ereal_Rep_distr_def)
  qed

  have \<mu>1_int: "\<And>y. (\<integral>\<^sup>+ x. ereal_Rep_distr \<mu>1 (x, y) \<partial>count_space UNIV) = ereal_Rep_distr mid y"
    unfolding mid_def apply simp
    apply (subst nn_integral_fst_count_space[symmetric])
    apply simp apply (subst indicator_singleton)
    unfolding ereal_indicator
    apply (subst nn_integral_singleton_indicator_countspace)
    by (auto) 

  have \<mu>2_int: "\<And>y. (\<integral>\<^sup>+ z. ereal_Rep_distr \<mu>2 (y, z) \<partial>count_space UNIV) = ereal_Rep_distr mid y"
    unfolding mid_def2 apply simp
    apply (subst nn_integral_snd_count_space[symmetric])
    apply simp apply (subst indicator_singleton)
    unfolding ereal_indicator
    apply (subst nn_integral_singleton_indicator_countspace)
    by (auto) 

  have yz_int: "\<And>y z. (\<integral>\<^sup>+ x. (f (x,y,z)) \<partial>count_space UNIV) = (ereal_Rep_distr \<mu>2 (y, z))"
    apply (subst f2) apply (subst nn_integral_multc) apply (auto)
    apply (subst \<mu>1_int) using mid0 unfolding ereal_Rep_distr_def by auto
  
  have xy_int: "\<And>x y. (\<integral>\<^sup>+z. (f (x,y,z)) \<partial>count_space UNIV) = (ereal_Rep_distr \<mu>1 (x, y))"
    apply (subst f3) apply (subst nn_integral_multc) apply (auto)
    apply (subst \<mu>2_int) using mid0' unfolding ereal_Rep_distr_def by auto
 
  have "(\<integral>\<^sup>+xyz. (f xyz) \<partial>count_space UNIV) = (\<integral>\<^sup>+yz. \<integral>\<^sup>+x. (f (x,yz)) \<partial>count_space UNIV \<partial>count_space UNIV)"
    by (subst nn_integral_snd_count_space, simp)
  also have "\<dots> = (\<integral>\<^sup>+yz. ereal_Rep_distr \<mu>2 yz \<partial>count_space UNIV)"
    apply (rule nn_integral_cong, rename_tac yz, case_tac yz, simp) apply (subst yz_int) by simp
  also have "\<dots> \<le> 1"
    by (simp add: ereal_Rep_distr_int_leq1)
  finally have leq1: "(\<integral>\<^sup>+xyz. (f xyz) \<partial>count_space UNIV) \<le> 1" by assumption

  have Rep_\<mu>: "ereal_Rep_distr \<mu> = f"
    unfolding \<mu>_def' apply (subst ereal_Abs_distr_inverse) 
    using leq1 by (auto simp: f_def)

  {fix x0 y0
  have "ereal_Rep_distr (apply_to_distr (\<lambda>(x,y,z). (x,y)) \<mu>) (x0,y0)
      = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. \<integral>\<^sup>+z. (f (x,y,z) * indicator {(x,y)} (x0, y0)) \<partial>count_space UNIV \<partial>count_space UNIV \<partial>count_space UNIV)"
    apply simp unfolding Rep_\<mu> 
    apply (subst nn_integral_fst_count_space[symmetric])
    apply (subst nn_integral_fst_count_space[symmetric])
    by simp
  also have "\<dots> = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. (ereal_Rep_distr \<mu>1 (x, y)) * (indicator {(x,y)} (x0, y0)) \<partial>count_space UNIV \<partial>count_space UNIV)"
    apply (subst nn_integral_multc) close 2
    apply (subst xy_int) by simp
  also have "\<dots> = ereal_Rep_distr \<mu>1 (x0, y0)"
    apply (subst nn_integral_fst_count_space)
    apply (subst indicator_singleton)
    apply (subst nn_integral_singleton_indicator_countspace)
    by (auto)
  also note calculation}
  thus "apply_to_distr (\<lambda>(x,y,z). (x,y)) \<mu> = \<mu>1"
    apply (subst ereal_Rep_distr_inject[symmetric])
    by (rule_tac ext, rename_tac xy0, case_tac xy0, simp)

  {fix y0 z0
  have "(ereal_Rep_distr (apply_to_distr (\<lambda>(x,y,z). (y,z)) \<mu>) (y0,z0))
      = (\<integral>\<^sup>+y. \<integral>\<^sup>+z. \<integral>\<^sup>+x. (f (x,y,z) * indicator {(y,z)} (y0,z0)) \<partial>count_space UNIV \<partial>count_space UNIV \<partial>count_space UNIV)"
    apply simp unfolding Rep_\<mu> 
    apply (subst nn_integral_snd_count_space[symmetric])
    by (subst nn_integral_fst_count_space[symmetric], simp)
  also have "\<dots> = (\<integral>\<^sup>+y. \<integral>\<^sup>+z. (ereal_Rep_distr \<mu>2 (y,z)) *  (indicator {(y,z)} (y0,z0)) \<partial>count_space UNIV \<partial>count_space UNIV)"
    apply (subst nn_integral_multc) close 2
    apply (subst yz_int) by simp
  also have "\<dots> = (ereal_Rep_distr \<mu>2 (y0, z0))"
    apply (subst nn_integral_fst_count_space)
    apply (subst indicator_singleton)
    apply (subst nn_integral_singleton_indicator_countspace)
    by (auto)
  also note calculation}
  thus "apply_to_distr (\<lambda>(x,y,z). (y,z)) \<mu> = \<mu>2"
    apply (subst ereal_Rep_distr_inject[symmetric])
    apply (rule_tac ext, rename_tac xy0, case_tac xy0)
    by metis

  show "ereal_Rep_distr (markov_chain_combine \<mu>1 \<mu>2) = f"
    using Rep_\<mu> \<mu>_def by auto
qed

lemma markov_chain:
  assumes "apply_to_distr snd \<mu>1 = apply_to_distr fst \<mu>2"
  defines "\<mu> == markov_chain_combine \<mu>1 \<mu>2"
  shows "apply_to_distr (\<lambda>(x::'a,y::'b,z::'c). (x,y)) \<mu> = \<mu>1" 
    and "apply_to_distr (\<lambda>(x,y,z). (y,z)) \<mu> = \<mu>2"
using assms markov_chain_combine_all by auto

lemma ereal_Rep_markov_chain: 
  assumes "apply_to_distr snd \<mu>1 = apply_to_distr fst \<mu>2"
  defines "\<mu> == markov_chain_combine \<mu>1 \<mu>2"
  defines "mid == apply_to_distr snd \<mu>1"
  defines "f == (\<lambda>(x,y,z). ereal_Rep_distr \<mu>1 (x,y) * ereal_Rep_distr \<mu>2 (y,z) / ereal_Rep_distr mid y)"
  shows "ereal_Rep_distr (markov_chain_combine \<mu>1 \<mu>2) = f"
unfolding assms(2-4) using assms(1) by (rule markov_chain_combine_all(3))

lemma markov_chain_support:
  assumes eq: "apply_to_distr snd \<mu>1 = apply_to_distr fst \<mu>2"
  assumes supp: "(x,y,z) \<in> support_distr (markov_chain_combine \<mu>1 \<mu>2)"
  shows "(x,y) \<in> support_distr \<mu>1"
    and "(y,z) \<in> support_distr \<mu>2"
proof -
  show "(x,y) \<in> support_distr \<mu>1"
    using supp unfolding support_distr_def' 
    apply (subst (asm) ereal_Rep_markov_chain)
      apply (fact eq)
    using less_eq_ereal_def by force
  show "(y,z) \<in> support_distr \<mu>2"
    using supp unfolding support_distr_def' 
    apply (subst (asm) ereal_Rep_markov_chain)
      apply (fact eq)
    using less_eq_ereal_def by force
qed

lemma compose_distr_cong: 
  fixes f1 f2 \<mu>
  assumes "\<And>x. x\<in>support_distr \<mu> \<Longrightarrow> f1 x = f2 x"
  shows "compose_distr f1 \<mu> = compose_distr f2 \<mu>"
proof -
  have aux: "\<And>x y. ereal_Rep_distr \<mu> y * ereal_Rep_distr (f1 y) x = ereal_Rep_distr \<mu> y * ereal_Rep_distr (f2 y) x"
    apply (case_tac "y\<in>support_distr \<mu>")
    using assms close auto
    unfolding support_distr_def' 
    using less_eq_ereal_def by fastforce
  show ?thesis
    apply (subst ereal_Rep_distr_inject[symmetric], rule ext)
    apply (subst ereal_Rep_compose_distr)+
    apply (rule nn_integral_cong)
    by (rule aux)
qed

lemma apply_to_distr_cong: 
  fixes f1 f2 \<mu>
  assumes "\<And>x. x\<in>support_distr \<mu> \<Longrightarrow> f1 x = f2 x"
  shows "apply_to_distr f1 \<mu> = apply_to_distr f2 \<mu>"
apply (subst compose_point_distr_l[symmetric])+
apply (rule compose_distr_cong)
using assms by auto


lemma apply_to_distr_0 [simp]: "apply_to_distr f 0 = 0"
  unfolding apply_to_distr_def apply simp
  unfolding zero_distr_def by auto

lemma apply_to_distr_compose_distr:
  shows "apply_to_distr f (compose_distr g h) = compose_distr (\<lambda>m. apply_to_distr f (g m)) h"
  by (metis (no_types, lifting) compose_distr_assoc compose_distr_cong compose_point_distr_l)

(* TODO move to Misc *)
lemma SUP_multc_ereal:
  fixes a::"_ \<Rightarrow> ereal"
  assumes pos: "b \<ge> 0" and finite: "b < \<infinity>" and notempty: "A \<noteq> {}"
  shows "(SUP i:A. a i*b) = (SUP i:A. a i)*b"
proof (rule SUP_eqI)
  fix i assume "i\<in>A"
  hence "a i \<le> (SUP i:A. a i)"
    by (simp add: SUP_upper)
  with pos show "a i * b \<le> (SUP i:A. a i) * b"
    using ereal_mult_right_mono by blast
next
  fix y assume bound: "\<And>i. i \<in> A \<Longrightarrow> a i * b \<le> y"
  show "(SUP i:A. a i) * b \<le> y" 
  proof (cases "b=0") 
    assume "b=0"
    with bound notempty have "y \<ge> 0" by auto
    with `b=0` show ?thesis by auto
  next
    assume "b\<noteq>0" with pos have pos': "b>0" by auto
    def y' == "y / b"
    with bound pos' finite have "\<And>i. i \<in> A \<Longrightarrow> a i \<le> y'"
      using ereal_divide_less_iff leD le_less_linear by blast 
    hence "(SUP i:A. a i) \<le> y'" 
      by (simp add: SUP_least)
    thus ?thesis
      unfolding y'_def using pos' finite 
      using ereal_divide_less_iff leD le_less_linear by blast 
  qed
qed

lemma apply_to_distr_sup:
  fixes \<mu>::"nat \<Rightarrow> 'a distr" and f::"'a \<Rightarrow> 'b"
  assumes inc: "incseq \<mu>"
  shows "apply_to_distr f (SUP i. \<mu> i) = (SUP i. apply_to_distr f (\<mu> i))"
proof -
  have inc': "incseq (\<lambda>i. apply_to_distr f (\<mu> i))"
    unfolding mono_def apply auto
    apply (rule mono_apply_to_distr[unfolded mono_def, rule_format])
    by (rule inc[unfolded mono_def, rule_format])
  have inc'': "\<And>x. incseq (\<lambda>xa a. ereal_Rep_distr (\<mu> xa) a * indicator {f a} x)"
    unfolding mono_def le_fun_def apply auto
    apply (rule ereal_mult_right_mono)
    using inc unfolding mono_def less_eq_distr_def' le_fun_def
    by auto
  have move_SUP: "ereal_Rep_distr (apply_to_distr f (SUP x. \<mu> x)) = (SUP i. ereal_Rep_distr (apply_to_distr f (\<mu> i)))"
    apply (rule ext) apply (simp add: ereal_Rep_apply_to_distr)
    apply (subst nn_integral_monotone_convergence_SUP[symmetric])
      close (fact inc'') close simp
    apply (subst ereal_Rep_SUP_distr)
     close (fact inc)
    apply (subst SUP_multc_ereal)
       unfolding ereal_indicator[symmetric]
       using PInfty_neq_ereal by auto
  show ?thesis
    apply (subst ereal_Rep_distr_inject[symmetric])
    apply (subst ereal_Rep_SUP_distr)
     using inc' move_SUP by simp_all
qed

lemma compose_distr_SUP_left:
  assumes "incseq f"
  shows "compose_distr (SUP n::nat. f n) \<mu> = (SUP n. compose_distr (f n) \<mu>)"
proof -
  have left_mono: "\<And>\<mu> y. mono (\<lambda>x. ereal_Rep_distr \<mu> y * x)" 
    unfolding mono_def apply auto
    apply (rule ereal_mult_left_mono)
    by auto

  have "ereal_Rep_distr (compose_distr (SUP x. f x) \<mu>) = (\<lambda>x. \<integral>\<^sup>+ a. ereal_Rep_distr \<mu> a * ereal_Rep_distr (SUP y. f y a) x \<partial>count_space UNIV)"
    by (simp add: ereal_Rep_compose_distr[THEN ext])
  also have "\<dots> = (\<lambda>x. \<integral>\<^sup>+ a. ereal_Rep_distr \<mu> a * (SUP i. ereal_Rep_distr (f i a)) x \<partial>count_space UNIV)"
    apply (subst ereal_Rep_SUP_distr)
     using assms unfolding mono_def le_fun_def by auto
  also have "... = (\<lambda>x. \<integral>\<^sup>+ a. (SUP i. ereal_Rep_distr \<mu> a * ereal_Rep_distr (f i a) x) \<partial>count_space UNIV)"
    apply (subst SUP_apply) 
    apply (subst SUP_ereal_mult_left[symmetric])
       by auto
  also have "... = (\<lambda>x. SUP i. \<integral>\<^sup>+ a. ereal_Rep_distr \<mu> a * ereal_Rep_distr (f i a) x \<partial>count_space UNIV)"
    apply (subst nn_integral_monotone_convergence_SUP)  
      apply (rule mono_funI) apply (rule mono_apply[OF left_mono])
      apply (rule mono_funD) apply (rule mono_apply[OF mono_ereal_Rep_distr])
      apply (rule mono_funD) close (fact assms)
     by auto
  also have "... = (SUP i. (\<lambda>x. \<integral>\<^sup>+ a. ereal_Rep_distr \<mu> a * ereal_Rep_distr (f i a) x \<partial>count_space UNIV))"
    by auto
  also have "... = (SUP i. ereal_Rep_distr (compose_distr (f i) \<mu>))"
    by (subst ereal_Rep_compose_distr[THEN ext], simp)
  also have "\<dots> = ereal_Rep_distr (SUP i. compose_distr (f i) \<mu>)"
    apply (rule ereal_Rep_SUP_distr[symmetric])
    apply (rule mono_apply[OF mono_compose_distr1])
    by (fact assms)

  finally show ?thesis
    apply (subst ereal_Rep_distr_inject[symmetric]) by assumption
qed

lemma support_distr_SUP: 
  assumes inc: "incseq \<mu>"
  shows "support_distr (SUP i. \<mu> i) = (SUP i. support_distr (\<mu> i))"
proof (unfold support_distr_def', auto)
  fix x assume "0 < ereal_Rep_distr (SUP n. \<mu> n) x"
  thus "\<exists>i. 0 < ereal_Rep_distr (\<mu> i) x"
    by (simp add: ereal_Rep_SUP_distr inc less_SUP_iff)
next
  fix x n assume "0 < ereal_Rep_distr (\<mu> n) x"
  thus "0 < ereal_Rep_distr (SUP n. \<mu> n) x "
    by (metis (mono_tags) SUP_apply SUP_lessD ereal_Rep_SUP_distr inc iso_tuple_UNIV_I less_linear less_not_sym)
qed


lemma Rep_apply_distr_biject:
  assumes "f (g x) = x"
  and "\<And>x. g (f x) = x"
  shows "Rep_distr (apply_to_distr f \<mu>) x = Rep_distr \<mu> (g x)"
apply (subst probability_singleton[symmetric])+
apply (subst probability_apply_to_distr)
apply (subgoal_tac "f -` {x} = {g x}")
using assms by auto
lemma ereal_Rep_apply_distr_biject:
  assumes "f (g x) = x"
  and "\<And>x. g (f x) = x"
  shows "ereal_Rep_distr (apply_to_distr f \<mu>) x = ereal_Rep_distr \<mu> (g x)"
unfolding ereal_Rep_distr_def apply (subst ereal.inject)
using assms by (rule Rep_apply_distr_biject)

lemma compose_distr_0 [simp]: "compose_distr (\<lambda>x. 0) \<mu> = 0"
  apply (subst ereal_Rep_distr_inject[symmetric])
  unfolding ereal_Rep_compose_distr[THEN ext]
  by simp
lemma compose_distr_0' [simp]: "compose_distr f 0 = 0"
  apply (subst ereal_Rep_distr_inject[symmetric])
  unfolding ereal_Rep_compose_distr[THEN ext]
  by simp




lemma compose_distr_const: "compose_distr (\<lambda>x. \<mu>) \<nu> = weight_distr \<nu> *\<^sub>R \<mu>"
  apply (subst ereal_Rep_distr_inject[symmetric]) apply (rule ext)
  unfolding ereal_Rep_compose_distr apply (subst Rep_distr_scaleR)
    close (rule probability_pos)
   close (rule probability_leq1)
  apply (subst nn_integral_multc)
    close simp
   close simp
  unfolding ereal_probability ereal_probability_def indicator_def 
  by simp


lemma compose_distr_add_left: 
  assumes "\<And>x. ereal_Rep_distr (f x) + ereal_Rep_distr (g x) = ereal_Rep_distr (h x)"
  shows "ereal_Rep_distr (compose_distr f \<mu>) + ereal_Rep_distr (compose_distr g \<mu>) = ereal_Rep_distr (compose_distr h \<mu>)"
apply (rule ext) unfolding plus_fun_def ereal_Rep_compose_distr assms[symmetric] 
apply (subst ereal_pos_distrib)
  close (fact ereal_Rep_distr_geq0)
 close (fact ereal_Rep_distr_not_inf)
apply (subst nn_integral_add)
by auto

lemma compose_distr_setsum_left: 
  assumes fin: "finite N"
  assumes sum: "\<And>x y. setsum (\<lambda>n. ereal_Rep_distr (f n x) y) N = ereal_Rep_distr (g x) y"
  shows "setsum (\<lambda>n. ereal_Rep_distr (compose_distr (f n) \<mu>)) N = ereal_Rep_distr (compose_distr g \<mu>)"
proof -
  def g' == "\<lambda>M x. ereal_Abs_distr (\<lambda>y. setsum (\<lambda>n. ereal_Rep_distr (f n x) y) M)"
  have leq1: "\<And>M x. M \<subseteq> N \<Longrightarrow> (\<integral>\<^sup>+ y. (\<Sum>n\<in>M. ereal_Rep_distr (f n x) y) \<partial>count_space UNIV) \<le> 1"
  proof -
    fix M and x assume MN: "M \<subseteq> N"
    have "(\<integral>\<^sup>+ y. (\<Sum>n\<in>M. ereal_Rep_distr (f n x) y) \<partial>count_space UNIV) \<le> (\<integral>\<^sup>+ y. (\<Sum>n\<in>N. ereal_Rep_distr (f n x) y) \<partial>count_space UNIV)"
      apply (rule nn_integral_mono, thin_tac _) 
      apply (rule setsum_mono3) using MN fin by auto
    also have "\<dots> \<le> (\<integral>\<^sup>+ y. (ereal_Rep_distr (g x) y) \<partial>count_space UNIV)"
      using sum by simp
    also have "\<dots> \<le> 1"
      by (rule ereal_Rep_distr_int_leq1)
    finally show "?thesis M x" by assumption
  qed
  have g'_rep: "\<And>M x. M \<subseteq> N \<Longrightarrow> ereal_Rep_distr (g' M x) = (\<lambda>y. setsum (\<lambda>n. ereal_Rep_distr (f n x) y) M)" 
    unfolding g'_def apply (rule ereal_Abs_distr_inverse)  
     close (rule setsum_nonneg, simp)
    by (fact leq1)
  have g': "g' N = g"
    apply (rule ext)
    apply (subst ereal_Rep_distr_inject[symmetric])
    apply (subst g'_rep)
    unfolding sum by auto
  have sum': "\<And>M x y. M \<subseteq> N \<Longrightarrow> setsum (\<lambda>n. ereal_Rep_distr (f n x) y) M = ereal_Rep_distr (g' M x) y"
    unfolding g'_rep by auto

  def M == N hence "M \<subseteq> N" by simp
  have M: "N = M" using M_def by simp
  (* show ?thesis *)
  have "setsum (\<lambda>n. ereal_Rep_distr (compose_distr (f n) \<mu>)) M = ereal_Rep_distr (compose_distr g \<mu>)"
    unfolding g'[symmetric] M
  using fin[unfolded M] sum'[unfolded M] `M \<subseteq> N` proof (induction M)
  case empty 
    hence "\<And>x y. ereal_Rep_distr (g' {} x) y = 0" by auto
    hence "\<And>x. g' {} x = 0" 
      apply (subst ereal_Rep_distr_inject[symmetric]) by auto
    thus ?case using zero_fun_def by auto
  next case (insert n M)
    have "(\<Sum>n\<in>insert n M. ereal_Rep_distr (compose_distr (f n) \<mu>))  
      = ereal_Rep_distr (compose_distr (f n) \<mu>) + (\<Sum>n\<in>M. ereal_Rep_distr (compose_distr (f n) \<mu>))"
      apply (rule setsum.insert)
      using insert.hyps by simp_all
    also have "\<dots> = ereal_Rep_distr (compose_distr (f n) \<mu>) + ereal_Rep_distr (compose_distr (g' M) \<mu>)"
      apply (subst insert.IH) apply (rule insert.prems) using insert.prems by auto
    also have "\<dots> = ereal_Rep_distr (compose_distr (g' (insert n M)) \<mu>)"
      apply (rule compose_distr_add_left)
      apply (subst g'_rep)
       using insert.prems close simp
      apply (subst g'_rep)
       using insert.prems close simp
      unfolding plus_fun_def
      apply (subst setsum.insert)
        using insert.hyps by auto
    finally show ?case by assumption
  qed
  thus ?thesis using M by simp
qed

lemma compose_distr_add_right: 
  assumes "\<And>x. ereal_Rep_distr \<mu> + ereal_Rep_distr \<nu> = ereal_Rep_distr \<sigma>"
  shows "ereal_Rep_distr (compose_distr f \<mu>) + ereal_Rep_distr (compose_distr f \<nu>) = ereal_Rep_distr (compose_distr f \<sigma>)"
apply (rule ext) unfolding plus_fun_def ereal_Rep_compose_distr assms[symmetric] 
apply (subst mult.commute, subst ereal_pos_distrib)
  close (fact ereal_Rep_distr_geq0)
 close (fact ereal_Rep_distr_not_inf)
apply (subst nn_integral_add) apply auto
by (metis (no_types, lifting) mult.commute nn_integral_cong) 


lemma compose_distr_setsum_right: 
  assumes fin: "finite N"
  assumes sum: "\<And>x y. setsum (\<lambda>n. ereal_Rep_distr (\<nu> n) y) N = ereal_Rep_distr \<mu> y"
  shows "setsum (\<lambda>n. ereal_Rep_distr (compose_distr f (\<nu> n))) N = ereal_Rep_distr (compose_distr f \<mu>)"
proof -
  def \<mu>' == "\<lambda>M. ereal_Abs_distr (\<lambda>y. setsum (\<lambda>n. ereal_Rep_distr (\<nu> n) y) M)"
  have leq1: "\<And>M. M \<subseteq> N \<Longrightarrow> (\<integral>\<^sup>+y. (\<Sum>n\<in>M. ereal_Rep_distr (\<nu> n) y) \<partial>count_space UNIV) \<le> 1"
  proof -
    fix M assume MN: "M \<subseteq> N"
    have "(\<integral>\<^sup>+ y. (\<Sum>n\<in>M. ereal_Rep_distr (\<nu> n) y) \<partial>count_space UNIV) \<le> (\<integral>\<^sup>+ y. (\<Sum>n\<in>N. ereal_Rep_distr (\<nu> n) y) \<partial>count_space UNIV)"
      apply (rule nn_integral_mono, thin_tac _) 
      apply (rule setsum_mono3) using MN fin by auto
    also have "\<dots> \<le> (\<integral>\<^sup>+ y. (ereal_Rep_distr \<mu> y) \<partial>count_space UNIV)"
      using sum by simp
    also have "\<dots> \<le> 1"
      by (rule ereal_Rep_distr_int_leq1)
    finally show "?thesis M" by assumption
  qed
  have \<mu>'_rep: "\<And>M. M \<subseteq> N \<Longrightarrow> ereal_Rep_distr (\<mu>' M) = (\<lambda>y. setsum (\<lambda>n. ereal_Rep_distr (\<nu> n) y) M)" 
    unfolding \<mu>'_def apply (rule ereal_Abs_distr_inverse)  
     close (rule setsum_nonneg, simp)
    by (fact leq1)
  have \<mu>': "\<mu>' N = \<mu>"
    apply (subst ereal_Rep_distr_inject[symmetric])
    apply (subst \<mu>'_rep) close simp
    unfolding sum by rule
  have sum': "\<And>M y. M \<subseteq> N \<Longrightarrow> setsum (\<lambda>n. ereal_Rep_distr (\<nu> n) y) M = ereal_Rep_distr (\<mu>' M) y"
    unfolding \<mu>'_rep by auto

  def M == N hence "M \<subseteq> N" by simp
  have M: "N = M" using M_def by simp
  (* show ?thesis *)
  have "setsum (\<lambda>n. ereal_Rep_distr (compose_distr f (\<nu> n))) M = ereal_Rep_distr (compose_distr f \<mu>)"
    unfolding \<mu>'[symmetric] unfolding M
  using fin[unfolded M] sum'[unfolded M] `M \<subseteq> N` proof (induction M)
  case empty
    hence "\<And>y. ereal_Rep_distr (\<mu>' {}) y = 0" by auto
    hence "\<And>y. \<mu>' {} = 0" 
      apply (subst ereal_Rep_distr_inject[symmetric]) by auto
    thus ?case using zero_fun_def by auto
  next case (insert n M)
    have "(\<Sum>n\<in>insert n M. ereal_Rep_distr (compose_distr f (\<nu> n)))  
      = ereal_Rep_distr (compose_distr f (\<nu> n)) + (\<Sum>n\<in>M. ereal_Rep_distr (compose_distr f (\<nu> n)))"
      apply (rule setsum.insert)
      using insert.hyps by simp_all
    also have "\<dots> = ereal_Rep_distr (compose_distr f (\<nu> n)) + ereal_Rep_distr (compose_distr f (\<mu>' M))"
      apply (subst insert.IH) apply (rule insert.prems) using insert.prems by auto
    also have "\<dots> = ereal_Rep_distr (compose_distr f (\<mu>' (insert n M)))"
      apply (rule compose_distr_add_right)
      apply (subst \<mu>'_rep)
       using insert.prems close simp
      apply (subst \<mu>'_rep)
       using insert.prems close simp
      unfolding plus_fun_def
      apply (subst setsum.insert)
        using insert.hyps by auto
    finally show ?case by assumption
  qed
  thus ?thesis using M by simp
qed

lemma apply_to_distr_setsum: 
  assumes fin: "finite N"
  assumes sum: "\<And>x y. setsum (\<lambda>n. ereal_Rep_distr (\<nu> n) y) N = ereal_Rep_distr \<mu> y"
  shows "setsum (\<lambda>n. ereal_Rep_distr (apply_to_distr f (\<nu> n))) N = ereal_Rep_distr (apply_to_distr f \<mu>)"
using assms unfolding compose_point_distr_l[symmetric]
by (rule compose_distr_setsum_right)

end