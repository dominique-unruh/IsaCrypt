theory ML_Term
  imports Main
begin
  
ML \<open>
  local
    structure Data = Generic_Data
    (
      type T = term
      val empty : T = @{term True}
      val extend = I;
      fun merge (t1,_) = t1
    );
    
    val get_term = Data.get 

    fun ml_term (ctx:Proof.context) (source:Symbol_Pos.T list) =
      let val range = Symbol_Pos.range source
          val str = Symbol_Pos.implode source
          val source' = Input.source true str range
          val ctx' = 
            ML_Context.expression range
              "term" "term"
              "fn ctx => set_term term ctx"
            (ML_Lex.read_source false source')
              (Context.Proof ctx)
          val term = get_term ctx'
       in
        term
      end
  in
    val set_term = Data.put
    fun ml_term_tr content (ctx:Proof.context) args =
      let fun err () = raise TERM ("string_tr", args) in
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) => c $ ml_term ctx (content (s, pos)) $ p
            | NONE => err ())
        | _ => err ())
      end;
  end;
\<close>
  
syntax "_ml_term" :: "cartouche_position \<Rightarrow> term" ("@_")
syntax "_ml_term" :: "cartouche_position \<Rightarrow> prop" ("PROP @_")
parse_translation \<open>[(@{syntax_const "_ml_term"}, 
    ml_term_tr (Symbol_Pos.cartouche_content o Symbol_Pos.explode))]\<close>


(* Testing *)
ML {* val test_goal = @{prop "1=2"} *}
lemma "a@bv==c"  oops
lemma "PROP @\<open>test_goal\<close>" oops

    
end
  