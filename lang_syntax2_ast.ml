type 'a symbol_parser = Symbol_Pos.T list -> 'a * Symbol_Pos.T list
type 'a ctx_sym_parser = Proof.context * Symbol_Pos.T list -> 'a * (Proof.context * Symbol_Pos.T list)

val spaces : unit symbol_parser = Scan.many (fn (s,_) => Symbol.is_blank s) >> (fn _ => ())

fun pos_of ((_,pos)::_) = pos
  | pos_of [] = Position.none
(* fun errmsg ((_,rest),SOME msg) = (fn _ => @{make_string} (msg(),pos_of rest))
  | errmsg ((_,rest),NONE) = (fn _ => @{make_string} ("Syntax error",pos_of rest)) *)
fun errmsg str parser = Scan.lift spaces |-- Scan.!! (fn ((_,syms),_) => fn _ => str() ^ Position.here (pos_of syms)) parser
fun fail_pos str = errmsg str (Scan.fail)
fun expect str = errmsg (fn _ => "expected "^str())
fun expect' str =                  errmsg (fn _ => "expected "^str)

val eof_parser : unit symbol_parser = spaces --| Scan.one (fn (s,_) => Symbol.is_eof s) >> (fn _ => ())

fun sym_parser sym = Parse.sym_ident :-- (fn s => if s=sym then Scan.succeed () else Scan.fail) >> #1;


(* A parse translation that translates cartouches using parser. *)
fun cartouche_tr what (parser:term ctx_sym_parser) (ctx:Proof.context) args =
    let fun err () = raise TERM ("cartouche_tr", args)
      in
      case args of
        [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
          (case Term_Position.decode_position p of
            SOME (pos, _) => 
              let val content = Symbol_Pos.cartouche_content (Symbol_Pos.explode (s, pos))
                  val range = if content=[] then (pos,pos) else Symbol_Pos.range content
                  val eof = (Symbol.eof, snd range)
                  val (term,_) = (Scan.error (errmsg (fn _=>"Could not parse "^what) (parser --| Scan.lift eof_parser))) (ctx,content@[eof])
              in
                c $ term $ p
              end
          | NONE => err ())
      | _ => err ()
    end;
