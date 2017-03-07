theory Scratch
imports Complex_Main 
begin

ML {*
    structure Data = Generic_Data
    (
      type T = term
      val empty : T = @{term True}
      val extend = I;
      fun merge (t1,_) = t1
    );
*}
    
ML {*
  val test_parser = Scan.lift Parse.nat |-- Args.term
*}

  
setup {*
    ML_Antiquotation.inline @{binding antiquotation_hack} (test_parser >> (ML_Syntax.atomic o ML_Syntax.print_term))
*}
    
  
ML {*
val pfx = (Input.source_content \<open>antiquotation_hack \<close> |> Symbol_Pos.explode0)
fun parse_cartouche ctx (cartouche:string) (pos:Position.T) : term = 
let val content = Symbol_Pos.cartouche_content (Symbol_Pos.explode (cartouche, pos))
    val antiq_body = pfx @ content
    val range = Symbol_Pos.range antiq_body
    val ml = [Antiquote.Antiq {body=antiq_body, range=range, start=fst range, stop=snd range}]
val _ = @{print} ml
    val ctx' = ML_Context.expression Position.no_range
              "term" "term" "fn ctx => Data.put term ctx"
              ml
              (Context.Proof ctx)
    val term = Data.get ctx'
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

term "(MY \<open>123 \<open>b+c\<close>\<close>, 3)" (* Should parse as (b+c,3) *)

  
end
