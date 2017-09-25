theory Tools 
imports "HOL.HOL"
keywords "close" :: "prf_script" % "proof"
begin

subsection {* "close" keyword *}

txt \<open>See @{file "tools.ML"}\<close>

subsection {* Simplifier modulo equivalence relation *}

txt {* See also @{url "http://stackoverflow.com/q/30573837/2646248"} *}

definition fun_equiv :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where "fun_equiv f x y == f x = f y"
lemma fun_equiv_refl: "fun_equiv f x x" by(simp add: fun_equiv_def)

ML_file "tools.ML"

end
