theory Scratch
imports Complex_Main 
begin

ML {*
  val times = Parse.sym_ident :-- (fn "*" => Scan.succeed () | _ => Scan.fail) >> #1;

  val test_parser = Scan.lift Parse.nat --| Scan.lift (times || Parse.reserved "x") -- Args.term
    >> (fn (n,t) => replicate n t |> HOLogic.mk_list dummyT)
*}



ML {*
fun errmsg (_,SOME msg) = msg
  | errmsg (_,NONE) = fn _ => "Syntax error"

fun parse_cartouche ctx (cartouche:string) (pos:Position.T) : term = 
  let val content = Symbol_Pos.cartouche_content (Symbol_Pos.explode (cartouche, pos))
      val toks = content |> Source.of_list 
           |> Token.source' true Keyword.empty_keywords
           |> Token.source_proper |> Source.exhaust
           |> (fn src => src @ [Token.eof])
      val (term,_) = Scan.error (Scan.!! errmsg (test_parser --| Scan.lift Parse.eof)) (Context.Proof ctx,toks)
  in term end
*}


ML {*
  (* Modified from Cartouche_Examples.thy *)
  fun cartouche_tr (ctx:Proof.context) args =
      let fun err () = raise TERM ("cartouche_tr", args) in
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) => c $ (parse_cartouche ctx s pos) $ p
            | NONE => err ())
        | _ => err ())
      end;
*}

syntax "_my_syntax" :: "cartouche_position \<Rightarrow> 'a" ("MY_")
parse_translation \<open>[(@{syntax_const "_my_syntax"}, cartouche_tr)]\<close>

term "(MY \<open>3 * \<open>b+c\<close>\<close>, 2)" (* Should parse as ([b+c,b+c,b+c],2) *)

  
end
