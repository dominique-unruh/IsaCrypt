theory LangSyntax2
imports Lang_Typed
begin

ML_file "lang_syntax2.ml"

ML {*
  val pattern_parser = Parse.short_ident >> (fn name => 
    Const(@{const_name variable_pattern},dummyT) $
      (Const(@{const_name LVariable},dummyT) $ HOLogic.mk_string name))
 |> Scan.lift

  fun get_context (ctx,rest) = (Context.the_proof ctx,rest)

  val balanced_text : Token.T list context_parser = Scan.many1 (fn tok => 
    not (Token.is_eof tok) andalso
    not (member (op=) [";","}"] (Token.content_of tok))) |> Scan.lift

  val expression_parser = balanced_text >> (fn text =>
    Const(@{const_name const_expression},dummyT) $ HOLogic.mk_string (@{make_string} text))

  (* val assign_symbol = sym_parser ":" *)

  val assign_parser = pattern_parser --| Scan.lift (Parse.$$$ ":=") -- expression_parser >> (fn (pat,exp) =>
    Const(@{const_name assign},dummyT) $ pat $ exp)
  
  fun eof [] = ((),[])
    | eof xs = Scan.fail_with (fn _ => fn _ => "expected EOF") xs
   
  val program_parser : term context_parser = assign_parser

  val program_keywords_raw = [":="]
  val program_keywords = Keyword.empty_keywords |> Keyword.add_keywords (map (fn k => ((k,Position.none),Keyword.no_spec)) program_keywords_raw)
*}

syntax "_program2" :: "cartouche_position \<Rightarrow> 'a" ("PR_")
parse_translation \<open>[(@{syntax_const "_program2"}, cartouche_tr program_keywords program_parser)]\<close>

term "PR\<open>x := 3+3\<close>"

  
end
