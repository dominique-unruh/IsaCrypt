theory LangSyntax2
imports Lang_Typed
begin
               
ML_file "lang_syntax2.ml"

ML {*
  fun filter (pred: 'a -> bool) (parser : 'b -> 'a*'b) (xs : 'b) =
    let val (res,xs') = parser xs in 
    if pred res then (res,xs')
    else Scan.fail xs end

(*  val scan_symid : string symbol_parser =
    spaces |--
    (Scan.many1 (Symbol.is_symbolic o Symbol_Pos.symbol) >> Symbol_Pos.implode) *)

  fun sym s = Scan.one (fn (s',_) => s=s')

  fun $$$ opname : string symbol_parser = 
    let fun sc [] : unit symbol_parser = Scan.succeed ()
          | sc (s::ss) = sym s |-- sc ss
    in
      spaces |-- sc (Symbol.explode opname) >> (fn _ => opname)
    end

  val identifier : string symbol_parser = spaces |-- Symbol_Pos.scan_ident >> Symbol_Pos.implode

  val pattern_parser : term ctx_sym_parser = identifier >> (fn name => 
    Const(@{const_name variable_pattern},dummyT) $
      (Const(@{const_name LVariable},dummyT) $ HOLogic.mk_string name))
 |> Scan.lift
  |> expect' "pattern"

  fun with_context (parser : Proof.context -> 'a ctx_sym_parser) : 'a ctx_sym_parser =
    fn arg as (ctx,_) => parser ctx arg
  fun with_pos (parser : Position.T -> 'a ctx_sym_parser) : 'a ctx_sym_parser =
    fn arg as (_,(_,pos)::_) => parser pos arg | arg => Scan.fail arg
    

  fun unscan tok res (ctx,toks) = (res,(ctx,tok::toks))

  fun any (ctx,tok::toks) = (tok,(ctx,toks))
    | any (st as (_,[])) = Scan.fail st

  val is_closing_brace = member op= [")","}","]","\<rangle>"]
  val is_opening_brace = AList.lookup op= [("(",")"), ("{","}"), ("[","]"), ("\<langle>","\<rangle>")]
  fun enclosed_text open_ close : Symbol_Pos.T list ctx_sym_parser = 
  any #-> (fn symp as (sym,_) =>
    if sym=close then Scan.succeed [symp]
    (* else if member op= stoppers sym then unscan symp [] *)
    else if is_closing_brace sym then Scan.fail
    else if Symbol.is_eof sym then Scan.fail
    else case is_opening_brace sym of 
      NONE => enclosed_text open_ close >> (curry op:: symp)
    | SOME close2 => enclosed_text symp close2 -- enclosed_text open_ close >> (fn (a,b) => symp::a@b)
  )
  |> expect (fn _ => close ^ " to match " ^ (fst open_) ^ Position.here (snd open_))
    
  fun balanced_text stoppers : Symbol_Pos.T list ctx_sym_parser = 
  any #-> (fn symp as (sym,_) =>
    if member op= stoppers sym then unscan symp []
    else if is_closing_brace sym then unscan symp []
    else if Symbol.is_eof sym then unscan symp []
    else case is_opening_brace sym of 
      NONE => balanced_text stoppers  >> (curry op:: symp)
    | SOME close2 => enclosed_text symp close2 -- balanced_text stoppers >> (fn (a,b) => symp::a@b)
  ) 
    
  val expression_parser = with_context (fn ctx => 
    Scan.lift spaces |-- balanced_text [";"] >> (fn symbols =>
      let val text = Symbol_Pos.implode symbols
          val term = Syntax.read_term ctx text
          val _ = @{print} term
      in Const(@{const_name const_expression},dummyT) $ term
      end))
    (* Const(@{const_name const_expression},dummyT) $ HOLogic.mk_string (@{make_string} (@{print}text))) *)
    (* |> Scan.lift *)
  |> expect' "expression"

  

  val assign_symbol = Scan.lift ($$$ ":=") |> expect' ":="

  val assign_parser : term ctx_sym_parser = pattern_parser --| assign_symbol -- expression_parser >> (fn (pat,exp) =>
    Const(@{const_name assign},dummyT) $ pat $ exp)
    |> expect' "assignment"
  
(*   fun eof [] = ((),[])
    | eof xs = Scan.fail_with (fn _ => fn _ => "expected EOF") xs *)
   
  val program_parser : term ctx_sym_parser = assign_parser

  (* val program_keywords_raw = [":="] *)
  (* val program_keywords = Keyword.empty_keywords |> Keyword.add_keywords (map (fn k => ((k,Position.none),Keyword.no_spec)) program_keywords_raw) *)
*}

syntax "_program2" :: "cartouche_position \<Rightarrow> 'a" ("PR_")
parse_translation \<open>[(@{syntax_const "_program2"}, cartouche_tr "program" program_parser)]\<close>

term "PR\<open>x := (3::nat)+3\<close>"

  
end
