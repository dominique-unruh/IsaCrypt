theory LangSyntax2
imports Lang_Typed
begin
               
ML_file "lang_syntax2.ml"

(* syntax "_internal_read_term_halfchecked_tag" :: "'a \<Rightarrow> 'a" ("INTERNALREADTERMHALFCHECKEDTAG _") *)
nonterminal internal_read_term_halfchecked
syntax "_internal_read_term_halfchecked_tag" :: "any \<Rightarrow> internal_read_term_halfchecked" ("_")

ML {*
local
  fun encode_str_tr' (s:string) = HOLogic.mk_string s
  fun decode_string (s:term) = HOLogic.dest_string s
  (* fun encode_str_tr' (s:string) = Free("\<open>"^s^"\<close>",dummyT) *)
  (* fun decode_string (Free(s,_)) = s *)                            

  fun encode_int_tr' (i:int) = Free(string_of_int i,dummyT)
  fun decode_int (t as Free(i,_)) = (case Int.fromString i of SOME i => i | _ => raise TERM ("decode_int",[t]))
    | decode_int t = raise TERM ("decode_int",[t])

  fun encode_sort_tr' ([]:sort) = Free("0",dummyT)
    | encode_sort_tr' (s::ss) = Free("s",dummyT) $ encode_str_tr' s $ encode_sort_tr' ss
  fun decode_sort (Free("0",_)) : sort = []
    | decode_sort (Free("s",_) $ s $ ss) = decode_string s :: decode_sort ss
    | decode_sort t = raise TERM("decode_sort",[t])

  fun encode_typ_list_tr' ([]:typ list) = Free("N",dummyT)
    | encode_typ_list_tr' (T::Ts) = Free("L",dummyT) $ encode_typ_tr' T $ encode_typ_list_tr' Ts
and
      encode_typ_tr' (TFree(n,s)) = Free("F",dummyT) $ encode_str_tr' n $ encode_sort_tr' s
    | encode_typ_tr' (Type(n,args)) = Free("T",dummyT) $ encode_str_tr' n $ encode_typ_list_tr' args

  fun decode_typ (Free("F",_) $ n $ s) = TFree(decode_string n, decode_sort s)
    | decode_typ (Free("T",_) $ n $ args) = Type(decode_string n, decode_typ_list args)
    | decode_typ t = raise TERM("decode_typ",[t])
  and
      decode_typ_list (Free("N",_)) = []
    | decode_typ_list (Free("L",_) $ T $ Ts) = decode_typ T :: decode_typ_list Ts
    | decode_typ_list t = raise TERM("decode_typ_list",[t])

  fun encode_term_tr' (t$u) = Free("$",dummyT) $ encode_term_tr' t $ encode_term_tr' u
    | encode_term_tr' (Free(n,T)) = Free("f",dummyT) $ encode_str_tr' n $ encode_typ_tr' T
    | encode_term_tr' (Const(n,T)) = Free("c",dummyT) $ encode_str_tr' n $ encode_typ_tr' T
    | encode_term_tr' (Abs(n,T,t)) = Free("a",dummyT) $ encode_str_tr' n $ encode_typ_tr' T $ encode_term_tr' t
    | encode_term_tr' (Var((n,i),T)) = Free("v",dummyT) $ encode_str_tr' n $ encode_int_tr' i $ encode_typ_tr' T
    | encode_term_tr' (Bound i) = Free("b",dummyT) $ encode_int_tr' i
in
  fun encode_term_tr _ [term] = encode_term_tr' term
    | encode_term_tr _ terms = raise TERM("encode_term_tr",terms)
  fun decode_term (Free("$",_) $ t $ u) = decode_term t $ decode_term u
    | decode_term (Free("f",_) $ n $ T) = Free(decode_string n, decode_typ T)
    | decode_term (Free("c",_) $ n $ T) = Const(decode_string n,decode_typ T)
    | decode_term (Free("a",_) $ n $ T $ t) = Abs(decode_string n, decode_typ T, decode_term t)
    | decode_term (Free("v",_) $ n $ i $ T) = Var ((decode_string n, decode_int i), decode_typ T)
    | decode_term (Free("b",_) $ i) = Bound (decode_int i)
    | decode_term t = raise TERM("decode_term",[t])
end
*}
  
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

  fun sympos_to_markup (sym,pos) = Markup.markup (Markup.properties (Position.properties_of pos) Markup.position) sym

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
  |> expect (fn _ => close ^ " to match " ^ sympos_to_markup open_)
    
  fun balanced_text stoppers : Symbol_Pos.T list ctx_sym_parser = 
  any #-> (fn symp as (sym,_) =>
    if member op= stoppers sym then unscan symp []
    else if is_closing_brace sym then unscan symp []
    else if Symbol.is_eof sym then unscan symp []
    else case is_opening_brace sym of 
      NONE => balanced_text stoppers  >> (curry op:: symp)
    | SOME close2 => enclosed_text symp close2 -- balanced_text stoppers >> (fn (a,b) => symp::a@b)
  ) 

  fun symbol_pos_list_to_string symbols : string= 
    let val (str,range) = Symbol_Pos.implode_range (Symbol_Pos.range symbols) symbols
        val text = Syntax.implode_input (Input.source false str range)
    in
      text
    end 

  fun read_term_halfchecked ctx symbols =
    let (* val tagged_str = "INTERNALREADTERMHALFCHECKEDTAG (" ^ symbol_pos_list_to_string symbols ^")"
val _ = @{print} tagged_str *)
        val str = symbol_pos_list_to_string symbols
        val encoded_term = Syntax.parse_term (Config.put Syntax.root @{nonterminal internal_read_term_halfchecked} ctx) str
        (* val _ = Syntax.read_term ctx str (* TODO: better way for reporting *) *)
        val term = decode_term encoded_term
    in                               
      term
    end


  val statement_stoppers = [";","}"]
    
  val expression_parser = with_context (fn ctx => 
    Scan.lift spaces |-- balanced_text statement_stoppers >> (fn symbols =>
      let val term = read_term_halfchecked ctx symbols
          (* val _ = @{print} term *)
      in Const(@{const_name const_expression},dummyT) $ term
      end))
    (* Const(@{const_name const_expression},dummyT) $ HOLogic.mk_string (@{make_string} (@{print}text))) *)
    (* |> Scan.lift *)
  |> expect' "expression"

  val assign_symbols = [":=","<-","\<leftarrow>"]

  val assign_symbol = Scan.lift (Scan.first (map $$$ assign_symbols)) |> expect' ":="

  val assign_parser : term ctx_sym_parser = pattern_parser --| assign_symbol -- expression_parser >> (fn (pat,exp) =>
    Const(@{const_name assign},dummyT) $ pat $ exp)
    |> expect' "assignment"
  
(*   fun eof [] = ((),[])
    | eof xs = Scan.fail_with (fn _ => fn _ => "expected EOF") xs *)
   
  val semicolon = Scan.lift ($$$ ";")

  val statement_parser : term ctx_sym_parser  = assign_parser

  fun program_seq_to_program [] = @{term Lang_Typed.skip}
    | program_seq_to_program [t] = t
    | program_seq_to_program (t::ts) = @{term seq} $ t $ program_seq_to_program ts

  fun statement_list_parser' st =
    (Scan.lift spaces |--
     Scan.ahead any #-> (fn (sym,_) =>
       if sym = "}" orelse Symbol.is_eof sym then Scan.succeed []
       else statement_parser --| Scan.option semicolon -- statement_list_parser' >> (op::)))
    st

  val statement_list_parser : term ctx_sym_parser = statement_list_parser' >> program_seq_to_program

  val program_parser : term ctx_sym_parser = statement_list_parser

  (* val program_keywords_raw = [":="] *)
  (* val program_keywords = Keyword.empty_keywords |> Keyword.add_keywords (map (fn k => ((k,Position.none),Keyword.no_spec)) program_keywords_raw) *)
*}

syntax "_program2" :: "cartouche_position \<Rightarrow> 'a" ("PR_")
parse_translation \<open>[(@{syntax_const "_program2"}, cartouche_tr "program" program_parser)]\<close>
syntax "_internal_read_term_halfchecked_tag" :: "'a \<Rightarrow> 'a"
parse_translation \<open>[(@{syntax_const "_internal_read_term_halfchecked_tag"}, encode_term_tr)]\<close>
syntax "_xxx" :: "'a \<Rightarrow> 'a" ("XXX_")
(* parse_ast_translation \<open>[(@{syntax_const "_xxx"}, fn ctx => fn asts => asts |> @{print} |> hd)]\<close> *)
parse_translation \<open>[(@{syntax_const "_xxx"}, fn ctx => fn asts => asts |> @{print} |> hd)]\<close>

  ML {* Syntax.parse_term @{context} "XXX(2+0)" *}
  
term "XXX(2+0)"

term "\<lambda>z. PR\<open>x := \<lambda>w. z+w+d; y <- d; y \<leftarrow> d()\<close>"
  
end
