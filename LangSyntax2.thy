theory LangSyntax2
  imports Lang_Typed Procs_Typed
begin
               
consts MODULE_FIELD_SELECTOR :: "string \<Rightarrow> 'a::procedure_functor \<Rightarrow> 'b"
nonterminal internal_read_term_halfchecked
syntax "_internal_read_term_halfchecked_tag" :: "any \<Rightarrow> internal_read_term_halfchecked" ("_")

ML_file "lang_syntax2.ml"

syntax "_program2" :: "cartouche_position \<Rightarrow> 'a" ("PR_")
parse_translation \<open>[(@{syntax_const "_program2"}, Lang_Syntax2.language_translation)]\<close>
syntax "_internal_read_term_halfchecked_tag" :: "'a \<Rightarrow> 'a"
parse_translation \<open>[(@{syntax_const "_internal_read_term_halfchecked_tag"}, Lang_Syntax2.encode_term_tr)]\<close>

  
(*ML\<open>
open Lang_Syntax2;;
  fun et open_ close : Symbol_Pos.T list ctx_sym_parser = 
  any #-> (fn symp as (sym,_) =>
    if sym=close then Scan.succeed [symp]
    else et open_ close >> (curry op:: symp)
  )
  |> expect (fn _ => close ^ " to match " ^ sympos_to_markup open_)
\<close>*)
  
ML \<open>val src = \<open>a bx c);\<close> |> Input.source_explode\<close>  
ML \<open>
(* val src = \<open>a bx c);\<close> |> Input.source_explode ;; *)
(* val b = Lang_Syntax2.balanced_text [";"] (@{context},src) *)
val c = Lang_Syntax2.enclosed_text ("(",Position.none) ")" (@{context},src)
(* val _ = Lang_Syntax2.expression_parser [";"] (@{context},src) *)
\<close>
  
  
(*setup {*
  Lang_Syntax2.insert_field_selector_thy "keygen" @{type_name EncScheme} @{const_name keygen''}
  #> Lang_Syntax2.insert_field_selector_thy "keygen" @{type_name Other} @{const_name keygen'}
  #> Lang_Syntax2.insert_field_selector_thy "enc" @{type_name EncScheme} @{const_name enc''}
  #> Lang_Syntax2.insert_field_selector_thy "enc" @{type_name Other} @{const_name enc'}
  #> Lang_Syntax2.insert_field_selector_thy "dec" @{type_name EncScheme} @{const_name dec''}
  #> Lang_Syntax2.insert_field_selector_thy "dec" @{type_name Other} @{const_name dec'}
*}*)
  
  (* TODO: automate this *)
abbreviation "MODULE_FIELD_SELECTOR_keygen" ("_ .keygen") where "X .keygen == MODULE_FIELD_SELECTOR ''keygen'' X"
abbreviation "MODULE_FIELD_SELECTOR_enc" ("_ .enc") where "X .enc == MODULE_FIELD_SELECTOR ''enc'' X"
abbreviation "MODULE_FIELD_SELECTOR_dec" ("_ .dec") where "X .dec == MODULE_FIELD_SELECTOR ''dec'' X"
abbreviation "MODULE_FIELD_SELECTOR_pick" ("_ .pick") where "X .pick == MODULE_FIELD_SELECTOR ''pick'' X"
abbreviation "MODULE_FIELD_SELECTOR_guess" ("_ .guess") where "X .guess == MODULE_FIELD_SELECTOR ''guess'' X"
  

setup {* Syntax_Phases.term_check 0 "module_field_selectors" (fn ctx => map (Lang_Syntax2.pick_field_selectors ctx)) 
            |> Context.theory_map *}
setup {* Syntax_Phases.term_check 1 "module_field_selectors" (fn ctx => fn ts => (map (Lang_Syntax2.unresolved_field_selectors ctx) ts; ts)) 
            |> Context.theory_map *}



  
  
  
(** Tests **)  
    
module_type ('pk::prog_type,'sk::prog_type,'m::prog_type,'c::prog_type) Other =
  keygen :: "(unit,'pk::prog_type*'sk::prog_type) procedure"
  enc :: "('pk*'m::prog_type, 'c::prog_type) procedure"
  dec :: "('sk*'c, 'm option) procedure"

  
module_type ('pk::prog_type,'sk::prog_type,'m::prog_type,'c::prog_type) EncScheme =
  keygen :: "(unit,'pk::prog_type*'sk::prog_type) procedure"
  enc :: "('pk*'m::prog_type, 'c::prog_type) procedure"
  dec :: "('sk*'c, 'm option) procedure"
print_theorems
  
ML \<open>
Procs_Typed.FieldSelector.get (Context.Proof @{context})
|> Symtab.dest |> map (apsnd Symtab.dest)
\<close>


  term \<open>  PR \<open>hoare {True} succ0 <@ G(m) {succ0}\<close>\<close>
  
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

  

term \<open> PR\<open>
proc () {
      x <$ uniform {0..<q};
      y <$ uniform {0..<q};
      b <@ E.keygen ();
      return b
    }
\<close>\<close>
  
(* term "A .enc" *)
end
  
term \<open>PR\<open>x <- (if b then m1 else m0)\<close>\<close>  
  
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
