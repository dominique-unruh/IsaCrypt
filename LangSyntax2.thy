theory LangSyntax2
  imports Lang_Typed Procs_Typed
      (* "~~/src/Tools/Adhoc_Overloading" (* REMOVE? *) *)
begin
               
consts MODULE_FIELD_SELECTOR :: "string \<Rightarrow> 'a::procedure_functor \<Rightarrow> 'b"
nonterminal internal_read_term_halfchecked
syntax "_internal_read_term_halfchecked_tag" :: "any \<Rightarrow> internal_read_term_halfchecked" ("_")

ML_file "lang_syntax2.ml"
  
syntax "_program2" :: "cartouche_position \<Rightarrow> 'a" ("PR_")
parse_translation \<open>[(@{syntax_const "_program2"}, Lang_Syntax2.program_translation)]\<close>
syntax "_internal_read_term_halfchecked_tag" :: "'a \<Rightarrow> 'a"
parse_translation \<open>[(@{syntax_const "_internal_read_term_halfchecked_tag"}, Lang_Syntax2.encode_term_tr)]\<close>

module_type ('pk::prog_type,'sk::prog_type,'m::prog_type,'c::prog_type) EncScheme =
  keygen'' :: "(unit,'pk::prog_type*'sk::prog_type) procedure"
  enc'' :: "('pk*'m::prog_type, 'c::prog_type) procedure"
  dec'' :: "('sk*'c, 'm option) procedure"

module_type ('pk::prog_type,'sk::prog_type,'m::prog_type,'c::prog_type) Other =
  keygen' :: "(unit,'pk::prog_type*'sk::prog_type) procedure"
  enc' :: "('pk*'m::prog_type, 'c::prog_type) procedure"
  dec' :: "('sk*'c, 'm option) procedure"


  (* TODO: automate this *)
setup {*
  Lang_Syntax2.insert_field_selector_thy "keygen" @{type_name EncScheme} @{const_name keygen''}
  #> Lang_Syntax2.insert_field_selector_thy "keygen" @{type_name Other} @{const_name keygen'}
  #> Lang_Syntax2.insert_field_selector_thy "enc" @{type_name EncScheme} @{const_name enc''}
  #> Lang_Syntax2.insert_field_selector_thy "enc" @{type_name Other} @{const_name enc'}
  #> Lang_Syntax2.insert_field_selector_thy "dec" @{type_name EncScheme} @{const_name dec''}
  #> Lang_Syntax2.insert_field_selector_thy "dec" @{type_name Other} @{const_name dec'}
*}
abbreviation "MODULE_FIELD_SELECTOR_keygen" ("_ .keygen") where "X .keygen == MODULE_FIELD_SELECTOR ''keygen'' X"
abbreviation "MODULE_FIELD_SELECTOR_enc" ("_ .enc") where "X .enc == MODULE_FIELD_SELECTOR ''enc'' X"
abbreviation "MODULE_FIELD_SELECTOR_dec" ("_ .dec") where "X .dec == MODULE_FIELD_SELECTOR ''dec'' X"
abbreviation "MODULE_FIELD_SELECTOR_pick" ("_ .pick") where "X .pick == MODULE_FIELD_SELECTOR ''pick'' X"
abbreviation "MODULE_FIELD_SELECTOR_guess" ("_ .guess") where "X .guess == MODULE_FIELD_SELECTOR ''guess'' X"
  
ML {*
(*fun find_selector _ (Type(@{type_name EncScheme},_)) "keygen" = Const(@{const_name keygen''},dummyT) |> SOME
  | find_selector _ (Type(@{type_name Other},_)) "keygen" = Const(@{const_name keygen'},dummyT) |> SOME
  | find_selector _ _ "keygen" = NONE
  | find_selector _ T name = raise TYPE("find_selector "^name,[T],[])*)

*}

setup {* Syntax_Phases.term_check 0 "module_field_selectors" (fn ctx => map (Lang_Syntax2.pick_field_selectors ctx)) 
            |> Context.theory_map *}
setup {* Syntax_Phases.term_check 1 "module_field_selectors" (fn ctx => fn ts => (map (Lang_Syntax2.unresolved_field_selectors ctx) ts; ts)) 
            |> Context.theory_map *}



experiment begin
term "x <$> y"

definition E :: "(int,int,int,int) EncScheme" where "E=undefined"
definition F :: "(int,int,int,int) Other" where "F=undefined"

term "(E).keygen"
  (* term "(A::unit).keygen" *)


term \<open>PR\<open>_<@ E.enc(3,4)\<close>\<close>
  
term "E .enc"
term "callproc ignore_pattern (E .enc) (const_expression (1,2))"
term "callproc ignore_pattern E .enc (const_expression (1,2))"

(* term "A .enc" *)
end
  
  
locale testtest begin
  definition "tralala" :: int where "tralala = 1"
  ML {* @{term "testtest.tralala"} *}  
end

ML {* @{term "testtest.tralala"} *}  
  
declare [[show_variants]]
term "enc0 <$> F"

term \<open> PR\<open>
proc () {
      x <$ uniform {0..<q};
      y <$ uniform {0..<q};
      b <@ E.keygen ();
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
