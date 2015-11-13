theory Lang_Simplifier
imports Tools Lang_Typed Hoare_Typed RHL_Typed
begin

named_theorems lang_simp_start
named_theorems lang_simp
named_theorems lang_cong

lemma lang_simp_start_denotation [lang_simp_start]: 
  "fun_equiv denotation c c' \<Longrightarrow> denotation c == denotation c'"
unfolding fun_equiv_def by simp

lemma lang_simp_start_hoare [lang_simp_start]: 
  "fun_equiv denotation c c' \<Longrightarrow> Hoare_Typed.hoare P c Q == Hoare_Typed.hoare P c' Q"
unfolding fun_equiv_def hoare_def by simp

lemma lang_simp_start_rhoare [lang_simp_start]: 
  "fun_equiv denotation c c' \<Longrightarrow> fun_equiv denotation d d' \<Longrightarrow> rhoare P c d Q == rhoare P c' d' Q"
unfolding fun_equiv_def rhoare_def by simp

simproc_setup hoare_simproc ("denotation c" | "Hoare_Typed.hoare P c Q" | "rhoare P' c d Q'") = {* 
  Tools.fun_equiv_simproc_named 
    @{named_theorems lang_simp_start}
    @{named_theorems lang_cong}
    @{named_theorems lang_simp}
*}

lemma lang_cong_program [lang_cong]: "fun_equiv denotation x y \<Longrightarrow> fun_equiv denotation (program x) (program y)"
  unfolding program_def .
lemma lang_cong_while [lang_cong]: "fun_equiv denotation x y \<Longrightarrow> fun_equiv denotation (Lang_Typed.while e x) (Lang_Typed.while e y)"
  SORRY
lemma lang_cong_seq [lang_cong]: "fun_equiv denotation x y \<Longrightarrow> fun_equiv denotation x' y' \<Longrightarrow> fun_equiv denotation (seq x x') (seq y y')"
  unfolding fun_equiv_def denotation_seq[THEN ext] by simp
lemma lang_cong_ifte [lang_cong]: "fun_equiv denotation x y \<Longrightarrow> fun_equiv denotation x' y' \<Longrightarrow> fun_equiv denotation (ifte e x x') (ifte e y y')"
  SORRY

lemma lang_simp_seq_assoc [lang_simp]: "fun_equiv denotation (seq x (seq y z)) (seq (seq x y) z)"
  unfolding fun_equiv_def by (fact denotation_seq_assoc[symmetric])
lemma lang_simp_skip_Seq [lang_simp]: "fun_equiv denotation (seq Lang_Typed.skip x) x"
  unfolding fun_equiv_def by (fact denotation_seq_skip)
lemma lang_simp_seq_skip [lang_simp]: "fun_equiv denotation (seq x Lang_Typed.skip) x"
  unfolding fun_equiv_def by (fact denotation_skip_seq)
lemma lang_simp_iftrue [lang_simp]: "(\<And>m. e_fun e m) \<Longrightarrow> fun_equiv denotation (ifte e c d) c"
  unfolding fun_equiv_def by (subst denotation_ifte[THEN ext], simp)
lemma lang_simp_iffalse [lang_simp]: "(\<And>m. \<not> e_fun e m) \<Longrightarrow> fun_equiv denotation (ifte e c d) d"
  unfolding fun_equiv_def by (subst denotation_ifte[THEN ext], simp)
lemma lang_simp_whilefalse [lang_simp]: "(\<And>m. \<not> e_fun e m) \<Longrightarrow> fun_equiv denotation (Lang_Typed.while e c) Lang_Typed.skip"
  (* unfolding fun_equiv_def by (subst denotation_while[THEN ext], simp) *)
  SORRY


lemma lang_simp_ifsame [lang_simp]: "fun_equiv denotation c d \<Longrightarrow> fun_equiv denotation (ifte e c d) c"
  unfolding fun_equiv_def by (subst denotation_ifte[THEN ext], auto)
lemma lang_simp_selfassign [lang_simp]: "(\<And>m. e_fun e m = memory_lookup m x) \<Longrightarrow> fun_equiv denotation (assign (variable_pattern x) e) Lang_Typed.skip"
  unfolding fun_equiv_def denotation_assign[THEN ext] denotation_skip[THEN ext] apply auto
  by (subst memory_update_lookup, simp)


experiment begin

  lemma "denotation PROGRAM[\<guillemotleft>x\<guillemotright>; {\<guillemotleft>y\<guillemotright>; \<guillemotleft>z\<guillemotright>}; \<guillemotleft>x\<guillemotright>] = denotation (foldr seq [x,y,z,x] Lang_Typed.skip)"
    apply simp unfolding program_def ..

  lemma "denotation PROGRAM[if ($x+1=$x+2-(1::int)) x:=x+1 else x:=x-1] = denotation PROGRAM[x:=x+1]"
    by simp

  lemma "denotation PROGRAM[if ($x=1) { while ($x=$x+(1::int)) { x:=x+1 } }; x:=x+1+2-3] = point_distr"
    by (simp add: program_def denotation_skip[THEN ext])

(*  lemma "LOCAL (x::int variable). hoare {True} x:=0; if ($x\<noteq>$x) { \<guillemotleft>c\<guillemotright> }; x:=x; x:=x+1 {$x=1}"
    by (simp, wp, skip, auto) *)
end

end
