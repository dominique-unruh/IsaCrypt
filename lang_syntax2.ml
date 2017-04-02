structure Lang_Syntax2 =
struct

structure ParseInfo = Proof_Data
(
  type T = {local_variables:typ Symtab.table}                                 
  val empty = {local_variables=Symtab.empty}
  fun init _ = empty
  (* val extend = I; *)
(*   fun merge ({local_variables=lv1},
             {local_variables=lv2}) =
    {local_variables=lv1@lv2} *)
);
fun update_local_variables {local_variables=_} lv : ParseInfo.T = {local_variables=lv}
fun add_local_variable var info = 
  case Symtab.lookup (#local_variables info) var of
    NONE => 
      let val typvar = TVar (("?lang", serial ()), [])
          val info' = update_local_variables info (Symtab.update_new (var,typvar) (#local_variables info))
          in
          (info',typvar)
          end
  | SOME typvar => (info,typvar)

(* type prog_parse = { program:term, local_variables:string list }
fun prog_parse t = { program=t, local_variables=[] }
fun merge_prog_parse t {local_variables=lv1,...} {local_variables=lv2,...} : prog_parse =
  { program=t,
    local_variables=lv1@lv2
  } *)

type 'a symbol_parser = Symbol_Pos.T list -> 'a * Symbol_Pos.T list
type 'a ctx_sym_parser = Proof.context * Symbol_Pos.T list -> 'a * (Proof.context * Symbol_Pos.T list)

val spaces : unit symbol_parser = Scan.many (fn (s,_) => Symbol.is_blank s) >> (fn _ => ())
fun any (ctx,tok::toks) = (tok,(ctx,toks))
  | any (st as (_,[])) = Scan.fail st

fun pos_of ((_,pos)::_) = pos
  | pos_of [] = Position.none
(* fun errmsg ((_,rest),SOME msg) = (fn _ => @{make_string} (msg(),pos_of rest))
  | errmsg ((_,rest),NONE) = (fn _ => @{make_string} ("Syntax error",pos_of rest)) *)
fun errmsg str parser = Scan.lift spaces |-- Scan.!! (fn ((_,syms),_) => fn _ => str() ^ Position.here (pos_of syms)) parser
fun fail_pos str = errmsg str (Scan.fail)
fun expect str = errmsg (fn _ => "expected "^str())
fun expect' str = errmsg (fn _ => "expected "^str)

val eof_parser : unit ctx_sym_parser = Scan.lift spaces --| 
  (Scan.one (fn (s,_) => Symbol.is_eof s) |> Scan.lift |> expect' "end of program") >> (fn _ => ())

(* fun sym_parser sym = Parse.sym_ident :-- (fn s => if s=sym then Scan.succeed () else Scan.fail) >> #1; *)


(* A parse translation that translates cartouches using parser. *)
fun cartouche_tr what (parser:term ctx_sym_parser) (ctx:Proof.context) arg =
    let fun err () = raise TERM ("cartouche_tr", [arg])
      in
      case arg of
        (c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p =>
          (case Term_Position.decode_position p of
            SOME (pos, _) => 
              let val content = Symbol_Pos.cartouche_content (Symbol_Pos.explode (s, pos))
                  val range = if content=[] then (pos,pos) else Symbol_Pos.range content
                  val eof = (Symbol.eof, snd range)
                  val (term,(ctx',_)) = (Scan.error (errmsg (fn _=>"Could not parse "^what) 
                                 (parser --| eof_parser))) (ctx,content@[eof])
              in
                (ctx', c $ term $ p)
              end
          | NONE => err ())
      | _ => err ()
    end;;

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
    | encode_typ_tr' (TVar((n,i),s)) = Free("V",dummyT) $ encode_str_tr' n $ encode_int_tr' i $ encode_sort_tr' s
    | encode_typ_tr' (Type(n,args)) = Free("T",dummyT) $ encode_str_tr' n $ encode_typ_list_tr' args

  fun decode_typ (Free("F",_) $ n $ s) = TFree(decode_string n, decode_sort s)
    | decode_typ (Free("V",_) $ n $ i $ s) = TVar((decode_string n, decode_int i), decode_sort s)
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
end;;

fun filter (pred: 'a -> bool) (parser : 'b -> 'a*'b) (xs : 'b) =
  let val (res,xs') = parser xs in 
  if pred res then (res,xs')
  else Scan.fail xs end

(*  val scan_symid : string symbol_parser =
    spaces |--
    (Scan.many1 (Symbol.is_symbolic o Symbol_Pos.symbol) >> Symbol_Pos.implode) *)

fun sym s = Scan.one (fn (s',_) => s=s')

fun $$$ opname : string ctx_sym_parser = 
  let fun sc [] : unit symbol_parser = Scan.succeed ()
        | sc (s::ss) = sym s |-- sc ss
  in
    spaces |-- sc (Symbol.explode opname) >> (fn _ => opname)
  end |> Scan.lift

val identifier : string symbol_parser = spaces |-- Symbol_Pos.scan_ident >> Symbol_Pos.implode

fun update_context f : 'a ctx_sym_parser = fn (ctx,toks) => let val (ctx',res) = f ctx in (res, (ctx', toks)) end

fun add_local_variable_parser var : typ ctx_sym_parser = update_context (fn ctx =>
  let val info = ParseInfo.get ctx
      val (info',typvar) = add_local_variable var info
      val ctx' = ParseInfo.put info' ctx
  in (ctx',typvar) end)

fun mk_lvar name typvar = Const(@{const_name LVariable},HOLogic.stringT --> Type(@{type_name variable},[typvar])) $ HOLogic.mk_string name

fun pattern_list_to_pair_pattern [] = @{term "ignore_pattern :: unit pattern"}
  | pattern_list_to_pair_pattern [a] = a
  (* | pattern_list_to_pair_pattern [a,b] = Const(@{const_name pair_pattern},dummyT) $ a $ b *)
  | pattern_list_to_pair_pattern (p::ps) = Const(@{const_name pair_pattern},dummyT) $ p $ pattern_list_to_pair_pattern ps

val variable_pattern_parser = Scan.lift identifier :-- add_local_variable_parser >> (fn (name,typvar) => Const(@{const_name variable_pattern},dummyT) $ mk_lvar name typvar)

fun tuple_pattern_parser st = ($$$ "(" |-- tuple_pattern_parser' >> pattern_list_to_pair_pattern) st
and tuple_pattern_parser' st = (Scan.lift spaces |-- Scan.ahead any :|-- (fn (sym,_) =>
  if sym = ")" then $$$ ")" >> (fn _ => [])
  else pattern_parser -- tuple_pattern_parser'' >> (op::))) st
and tuple_pattern_parser'' st = (Scan.lift spaces |-- (Scan.first (map $$$ [",",")"]) |> expect' ", or )")
  :|-- (fn sym =>
    if sym = ")" then Scan.succeed []
    else if sym = "," then pattern_parser -- tuple_pattern_parser'' >> (op::)
    else Scan.fail)) st
and pattern_parser st = 
      ((Scan.lift spaces |--
       Scan.ahead any #-> (fn (sym,_) =>
         if sym = "(" then tuple_pattern_parser
         else if sym = "_" then $$$ "_" |-- Scan.succeed (Const(@{const_name ignore_pattern},dummyT))
         else variable_pattern_parser))
      |> expect' "pattern") st

fun with_context (parser : Proof.context -> 'a ctx_sym_parser) : 'a ctx_sym_parser =
  fn arg as (ctx,_) => parser ctx arg
fun with_pos (parser : Position.T -> 'a ctx_sym_parser) : 'a ctx_sym_parser =
  fn arg as (_,(_,pos)::_) => parser pos arg | arg => Scan.fail arg
    

  fun unscan tok res (ctx,toks) = (res,(ctx,tok::toks))


  fun sympos_to_markup (sym,pos) = Markup.markup (Markup.properties (Position.properties_of pos) Markup.position) sym

  val is_closing_brace = member op= [")","}","]","\<rangle>"]
  val is_opening_brace = AList.lookup op= [("(",")"), ("{","}"), ("[","]"), ("\<langle>","\<rangle>")]

  (* Parses "stuff)" where ")" is the parenthesis given as "close". "open_" is the matching
     parenthesis already parsed (used for messages) *)
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
    
  fun expression_parser stoppers : term ctx_sym_parser = with_context (fn ctx => 
    Scan.lift spaces |-- balanced_text stoppers >> (fn symbols =>
      let val term = read_term_halfchecked ctx symbols
          (* val _ = @{print} term *)
      in Const("_expression",dummyT) $ term
      end))
  |> expect' "expression"

  val paren_expression_parser : term ctx_sym_parser = with_context (fn ctx => 
    (Scan.one (fn (s,_) => s="(") |> Scan.lift) :|-- 
    (fn open_ => enclosed_text open_ ")" >> (fn symbols =>
      let val term = read_term_halfchecked ctx (open_::symbols)
      in Const("_expression",dummyT) $ term
      end)))
  |> expect' "expression (in parentheses)"

  val assign_symbols = [":=","<-","\<leftarrow>"]
  val sample_symbols = ["<$","<-$","\<leftarrow>$"]
  val call_symbols = ["<@"]
  val assignlike_symbols = assign_symbols @ sample_symbols @ call_symbols
  val assignlike_symbols_or = String.concatWith " or " assignlike_symbols 

  val assignlike_symbol = Scan.first (map $$$ assignlike_symbols) |> expect' assignlike_symbols_or

  val function_identifier = Scan.lift identifier >> (fn name => Free(name,dummyT))

(*
  val arglist_stoppers = [")",","]

fun call_args_no_open' st = (Scan.lift spaces |-- (Scan.first (map $$$ [",",")"]) |> expect' ", or )")
  :|-- (fn sym =>
    if sym = ")" then Scan.succeed []
    else if sym = "," then expression_parser arglist_stoppers -- call_args_no_open' >> (op::)
    else Scan.fail)) st
val call_args_no_open : term list ctx_sym_parser = (Scan.lift spaces |-- Scan.ahead any :|-- (fn (sym,_) =>
    if sym = ")" then $$$ ")" >> (fn _ => [])
    else expression_parser arglist_stoppers -- call_args_no_open' >> (op::)))

fun mk_prod (t1, t2) = Const (@{const_name Product_Type.Pair}, dummyT) $ t1 $ t2

fun mk_tuple [] = @{term "()"}
  | mk_tuple ts = foldr1 mk_prod ts;
*)

val call_parser : (term*term) ctx_sym_parser = 
  function_identifier -- paren_expression_parser
  >> (fn (proc,args) => (proc, args))

val assign_parser : term ctx_sym_parser = pattern_parser -- assignlike_symbol :|-- (fn (pat,sym) =>
  if member op= assign_symbols sym then expression_parser statement_stoppers >> (fn exp => Const(@{const_name assign},dummyT) $ pat $ exp)
  else if member op= sample_symbols sym then expression_parser statement_stoppers >> (fn exp => Const(@{const_name sample},dummyT) $ pat $ exp)
  else if member op= call_symbols sym then call_parser >> (fn (proc,args) => Const(@{const_name callproc},dummyT) $ pat $ proc $ args)
  else error ("internal error: unexpected symbol "^sym))
  |> expect' "assignment"
  
(*   fun eof [] = ((),[])
    | eof xs = Scan.fail_with (fn _ => fn _ => "expected EOF") xs *)
   
  val semicolon = $$$ ";"

  val statement_parser : term ctx_sym_parser  = assign_parser

fun program_seq_to_program [] = @{term Lang_Typed.skip}
  | program_seq_to_program [t] = t
  | program_seq_to_program (t::ts) = 
        @{term seq} $ t $ program_seq_to_program ts

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


fun subst_lvars lvars (v as Free(x,T)) =
  (case Symtab.lookup lvars x of
    NONE => v
  | SOME typvar => 
      if T<>dummyT then raise TERM("subst_lvars",[v])
      else mk_lvar x typvar)
  | subst_lvars lvars (a$b) = subst_lvars lvars a $ subst_lvars lvars b
  | subst_lvars lvar (Abs(n,T,t)) = Abs(n,T,subst_lvars lvar t)
  | subst_lvars _ t = t

(* TODO: should abstract lvars *)
fun create_expression lvars t = 
  let 
    val frees = Term.add_free_names t [] |> sort_distinct string_ord |> List.mapPartial (Symtab.lookup_key lvars)
    (* val _ = @{print} (t,frees) *)
    val abs = fold_rev (fn (x,T) => fn t => Abs(x,T,abstract_over(Free(x,dummyT),t))) frees t
    val appl = fold (fn (x,T) => fn t => Const(@{const_name apply_expression},dummyT) $ t $ mk_lvar x T) frees
                    (Const(@{const_name const_expression},dummyT) $ abs)
    (* val _ = @{print} appl *)
  in
    appl
  end

fun process_expressions lvars (Const("_expression",_) $ t) = create_expression lvars t
  | process_expressions lvars (a$b) = process_expressions lvars a $ process_expressions lvars b
  | process_expressions lvars (Abs (n,T,t)) = Abs (n,T,process_expressions lvars t)
  | process_expressions _ t = t

fun process_program ctx (program:term) = 
  let val info = ParseInfo.get ctx
      val lvars = #local_variables info
      (* val _ = @{print}("locals",Symtab.dest lvars) *)
      (* val program = subst_lvars lvars program (* Should not be done. Instead, create_expression should handle lvars *) *)
      val program = process_expressions lvars program
      (* val _ = @{print}("prog",program) *)
  in
  program
  end

fun program_translation ctx [arg] =
  let val (ctx',raw_program) = cartouche_tr "program" program_parser ctx arg
  in
    process_program ctx' raw_program
  end
| program_translation _ args = raise TERM ("program_translation", args)

end