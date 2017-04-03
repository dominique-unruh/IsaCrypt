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

(* declare [[ML_exception_trace]] *)
  
term \<open> PR\<open>
proc () {
      x <$ uniform {0..<q};
      y <$ uniform {0..<q};
      b <@ A (g^x, g^y, g^(x*y));
      return b
    }
\<close>\<close>
  
term \<open>PR\<open>proc (x,y) { x <- 1::int; return x+3; }\<close>\<close>
term \<open>PR\<open>b <@ A(g^x)\<close>\<close>
term "PR\<open> _ <@ A(g^x, g^y, g^(x+y)); \<close>"
term \<open>PR\<open> x <$ uniform {0..<q} \<close>\<close>
term "PR\<open>y <- 1\<close>"
term "PR\<open>(_,_) \<leftarrow> (1,x)\<close>"
term "PR\<open>y <- x; y <- z; q <- (1,fst (y,q)); q <- w\<close>"
term "\<lambda>z. PR\<open>x := \<lambda>w. z+w+d; y <- (x,x); y \<leftarrow> e()\<close>"
term \<open>\<lambda>z. PR\<open>z:=1; x := z;\<close>\<close>
term "(1,(2,3))"
  
end
