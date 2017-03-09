fun sym_parser sym = Parse.sym_ident :-- (fn s => if s=sym then Scan.succeed () else Scan.fail) >> #1;

(* parse_cartouche: This function takes the cartouche that should be parsed (as a plain string
   without markup), together with its position. (All this information can be extracted using the 
   information available to a parse translation, see cartouch_tr below.) *)
fun parse_cartouche keywords (parser:'a context_parser) ctx (cartouche:string) (pos:Position.T) : 'a = 
  let 
    (* This extracts the content of the cartouche as a "Symbol_Pos.T list".
       One posibility to continue from here would be to write a parser that works
       on "Symbol_Pos.T list". However, most of the predefined parsers expect 
       "Token.T list" (a single token may consist of several symbols, e.g., 123 is one token). *)
    val content = Symbol_Pos.cartouche_content (Symbol_Pos.explode (cartouche, pos))
    (* Translate content into a "Token.T list". *)
    val toks = content |> Source.of_list (* Create a "Source.source" containing the symbols *)
      |> Token.source' true keywords (* Translate into a "Source.source" containing tokens.
             I don't know what the argument true does here. false also works, I think. *)
      |> Token.source_proper (* Remove things like whitespaces *)
      |> Source.exhaust (* Translate the source into a list of tokens *)
      |> (fn src => src @ [Token.eof]) (* Add an eof to the end of the token list, to enable Parse.eof below *)
val _ = @{make_string} toks |> warning
    (* A conversion function that produces error messages. The ignored argument here
       contains the context and the list of remaining tokens, if needed for constructing
       the message. *)
    fun errmsg (_,SOME msg) = msg
      | errmsg (_,NONE) = fn _ => "Syntax error"
    (* Apply the parser. We additionally combine it with Parse.eof to ensure that 
       the parser parses the whole text (till EOF). And we use Scan.!! to convert parsing failures 
       into parsing errors, and Scan.error to report parsing errors to the toplevel. *)
    val (term,_) = Scan.error (Scan.!! errmsg (parser --| Scan.lift Parse.eof)) (Context.Proof ctx,toks)
  in term end

(* A parse translation that translates cartouches using parser. The code is very close to 
   the examples from Cartouche_Examples.thy. It takes a given cartouche-subterm, gets its 
   position, and calls parse_cartouche to do the translation to a term. *)
fun cartouche_tr keywords (parser:term context_parser) (ctx:Proof.context) args =
    let fun err () = raise TERM ("cartouche_tr", args) in
      (case args of
        [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
          (case Term_Position.decode_position p of
            SOME (pos, _) => c $ (parse_cartouche keywords parser ctx s pos) $ p
          | NONE => err ())
      | _ => err ())
    end;
