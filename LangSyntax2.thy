theory LangSyntax2
imports Lang_Typed
begin
               
nonterminal internal_read_term_halfchecked
syntax "_internal_read_term_halfchecked_tag" :: "any \<Rightarrow> internal_read_term_halfchecked" ("_")

ML_file "lang_syntax2.ml"

syntax "_program2" :: "cartouche_position \<Rightarrow> 'a" ("PR_")
parse_translation \<open>[(@{syntax_const "_program2"}, Lang_Syntax2.program_translation)]\<close>
syntax "_internal_read_term_halfchecked_tag" :: "'a \<Rightarrow> 'a"
parse_translation \<open>[(@{syntax_const "_internal_read_term_halfchecked_tag"}, Lang_Syntax2.encode_term_tr)]\<close>
(* syntax "_expression" :: "'a \<Rightarrow> 'a" *)

term "PR\<open>y <- 1\<close>"

term "PR\<open>y <- x; y <- z; q <- (1,fst (y,q)); q <- w\<close>"

term "\<lambda>z. PR\<open>x := \<lambda>w. z+w+d; y <- (x,x); y \<leftarrow> e()\<close>"

term \<open>\<lambda>z. PR\<open>x := z;\<close>\<close>
  
end
