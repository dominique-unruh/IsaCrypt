structure Extended_Sorry =
struct

type annotation = {
  thy:theory,
  prop:term,
  message:string option,
  position:Position.T
};

fun annotate_prop (annot:annotation) : cterm =
  let val annot_prop = #prop annot
      val annot_pos = #position annot |> Term_Position.encode |> HOLogic.mk_string
      val annot_msg = case #message annot of NONE => @{term "None::string option"} | SOME msg => @{term "Some::string\<Rightarrow>_"} $ HOLogic.mk_string msg
      val generalized_prop = Var (("A", 0), propT)
  in
  Logic.implies $ (HOLogic.mk_Trueprop (@{term ANNOTATION} $ annot_prop $ annot_msg $ annot_pos)) $ generalized_prop |>
  cterm_of (#thy annot)
  end;

val (_, make_thm_cterm_annot) =
  Context.>>>
    (Context.map_theory_result (Thm.add_oracle (Binding.make ("skip_proof", @{here}), annotate_prop)));

fun make_thm_annot annot = make_thm_cterm_annot annot OF @{thms ANNOTATION};

fun cheat_tac_annot msg pos i st =
  SUBGOAL (fn (goal,i) =>
    rtac (make_thm_annot {thy=Thm.theory_of_thm st, prop=goal, position=pos, message=msg}) i) i st;

local
fun ora_of seen (PBody {oracles, thms, ...}) found path = 
  let val found = if null oracles then found else (path,oracles)::found
      val (found,seen) = fold (fn (i, (name,_,body)) => fn (found,seen) =>
                               if Inttab.defined seen i then (found,seen)
                               else (ora_of (Inttab.update (i,()) seen) (Future.join body) found (name::path)))
                         thms (found,seen)
  in
  (found,seen)
  end
in
fun all_oracles_of thm = ora_of Inttab.empty (Thm.proof_body_of thm) [] [] |> fst |> rev
end

fun markup_thm_name ctx name =
  let val namespace = Global_Theory.facts_of (Proof_Context.theory_of ctx) |> Facts.space_of
      val (markup,name) = Name_Space.markup_extern ctx namespace name
  in
  Markup.markup markup name  
  end;

type print_annotated_conf = {
  show_empty: bool
};

val print_annotated_conf_default = {
  show_empty=false
};

fun print_annotated_oracles (conf:print_annotated_conf) ctx thm =
  let fun render_annot prop msg pos = 
         let val prop_str = Syntax.pretty_term ctx prop |> Pretty.str_of
             val msg_str = (case msg of Const(@{const_name None},_) => ""
                                      | Const(@{const_name Some},_)$str => " ("^HOLogic.dest_string str^")"
                                      | t => raise (TERM("parsing annotation, message",[t])))
             val pos = pos |> HOLogic.dest_string |> Term_Position.decode |> the
             val pos_str = Markup.markup (Markup.properties (Position.properties_of pos) Markup.position) "[here]"
         in
          prop_str ^ msg_str ^ " " ^ pos_str
         end
      fun extract_annot trm = 
        Logic.dest_implies trm |> fst
        |> HOLogic.dest_Trueprop
        |> (fn (Const(@{const_name ANNOTATION},_)$prop$msg$pos) => render_annot prop msg pos | t => raise (TERM("parsing annotation",[t])))
        handle TERM _ => "[--unknown data--]"
      fun ora_to_str (name,term) = 
        if name="Extended_Sorry.skip_proof" then "  sorry: "^(term |> extract_annot)
        else if name="Pure.skip_proof" then "  sorry"
        else "  "^name^": "^(Syntax.pretty_term ctx term |> Pretty.string_of)
      fun path_to_str path = 
        let val path = if #show_empty conf
                       then map (fn "" => "<anonymous>" | x => x) path
                       else filter (fn x=>x<>"") path
            val path = map (markup_thm_name ctx) path
            val path = rev path
        in String.concatWith " > " path end
      fun thm_to_str (path,oras) =
        (path_to_str path)::(map ora_to_str oras)
  in
  thm |> all_oracles_of |> map thm_to_str |> List.concat |> String.concatWith "\n" |> writeln
  end;

val _ = let
fun print thms ctxt =
  (Attrib.eval_thms ctxt thms |> map (print_annotated_oracles print_annotated_conf_default ctxt); ctxt)
in
Outer_Syntax.local_theory @{command_spec "print_sorry"}
"show all occurrences of sorry (and other oracles)"
(Parse_Spec.xthms1 >> print)
end;


(** Method sorry **)

fun cheating msg pos ctxt int = METHOD (fn _ => fn st =>
  if int orelse Config.get ctxt quick_and_dirty then
    ALLGOALS (cheat_tac_annot msg pos) st
  else error "Cheating requires quick_and_dirty mode!");

fun sorry_text msg pos int = Method.Basic (fn ctxt => cheating msg pos ctxt int);

fun proof_global_skip_proof msg pos int state =
  Proof.global_terminal_proof ((sorry_text msg pos int, Position.no_range), NONE) state before
  Skip_Proof.report (Proof.context_of state);
fun proof_local_skip_proof msg pos int state =
  Proof.local_terminal_proof ((sorry_text msg pos int, Position.no_range), NONE) state before
  Skip_Proof.report (Proof.context_of state);

fun local_skip_proof msg pos = Toplevel.proof' (proof_local_skip_proof msg pos);
fun global_skip_proof msg pos = Toplevel.end_proof (proof_global_skip_proof msg pos);
fun skip_proof msg pos = (local_skip_proof msg pos) o (global_skip_proof msg pos);

fun parse_position toks = (Token.pos_of (hd toks), toks);

val _ = Outer_Syntax.command @{command_spec "SORRY"} "skip proof (quick-and-dirty mode only!)"
    (parse_position -- Scan.option Parse.string >> (fn (pos,msg) => skip_proof msg pos));

end
