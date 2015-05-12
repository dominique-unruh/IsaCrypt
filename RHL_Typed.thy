theory RHL_Typed
imports RHL_Untyped Lang_Typed
begin

subsection {* Definition *}

definition rhoare :: "(memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> program \<Rightarrow> (memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "rhoare pre c1 c2 post =
  (\<forall>m1 m2. pre m1 m2 \<longrightarrow> 
     (\<exists>\<mu>. apply_to_distr fst \<mu> = denotation c1 m1
        \<and> apply_to_distr snd \<mu> = denotation c2 m2
        \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> post m1' m2')))"

lemma rhoare_untyped: "rhoare P c1 c2 Q = rhoare_untyped P (mk_program_untyped c1) (mk_program_untyped c2) Q"
  unfolding rhoare_def rhoare_untyped_def denotation_def ..

subsection {* Concrete syntax *}

syntax "_rhoare" :: "(memory \<Rightarrow> bool) \<Rightarrow> program_syntax \<Rightarrow> program_syntax \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> term"
          ("hoare {(_)}/ (2_) ~ (2_)/ {(_)}")
syntax "_memory" :: memory ("&m")
syntax "_memory1" :: memory ("&1")
syntax "_memory2" :: memory ("&2")
syntax "_select_memory1" :: "'a \<Rightarrow> 'a" ("_\<^sub>1" [1000] 1000)
syntax "_select_memory2" :: "'a \<Rightarrow> 'a" ("_\<^sub>2" [1000] 1000)

ML_file "rhoare_syntax.ML"

parse_translation {*
  let
  in
    [("_rhoare", fn ctx => fn [P,c1,c2,Q] => RHoare_Syntax.trans_hoare ctx P c1 c2 Q)]
  end
*}

(*
term "x\<^sub>a"
ML {* @{print} @{term x\<^sub>a} *}

consts x::"int variable"
consts f::"memory\<Rightarrow>memory"
term "hoare {(x)\<^sub>1 = undefined} skip ~ skip {undefined}"
*)

subsection {* Rules *}

(*
definition "blockassign (xs::'a::procargs procargvars) (es::'a procargs) == 
  Abs_program
  (fold 
  (\<lambda>(x,e) p. Seq p (Assign x e))
  (zip (mk_procargvars_untyped xs) (mk_procargs_untyped es))
  Skip)"


lemma callproc_equiv:
  fixes x p e
  defines "V_e == set [v. e \<leftarrow> mk_procargs_untyped e, v \<leftarrow> eu_vars e]"
  defines "V_p == set (vars (p_body p)) \<union> set (mk_procargvars_untyped (p_args p)) \<union> set (e_vars (p_return p))"
  assumes "V_p \<inter> V = {}" and "V_p \<inter> V_e = {}"
  shows "hoare {\<forall>x\<in>V. memory_lookup_untyped &1 x = memory_lookup_untyped &2 x} 
                  \<guillemotleft>callproc x p e\<guillemotright> ~ \<guillemotleft>blockassign (p_args p) e\<guillemotright>; \<guillemotleft>p_body p\<guillemotright>; x := \<guillemotleft>p_return p\<guillemotright>
               {\<forall>x\<in>V. memory_lookup_untyped &1 x = memory_lookup_untyped &2 x}"
*)

(* TODO *)

end
