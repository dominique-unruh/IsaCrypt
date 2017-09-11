structure Wlog =
struct

(* Like Facts.dest_static, but also returns facts that have been overwritten with a new fact of the same name *)
fun dest_static2 ctx verbose prev_facts facts =
  let val ctx_generic = Context.Proof ctx
      fun thms_eq [] [] = true
        | thms_eq (_::_) [] = false
        | thms_eq [] (_::_) = false
        | thms_eq (t::ts) (u::us) = Thm.prop_of t = Thm.prop_of u
                                    andalso Thm.shyps_of t = Thm.shyps_of u
                                    andalso Thm.hyps_of t = Thm.hyps_of u
                                    andalso Thm.tpairs_of t = Thm.tpairs_of u
                                    (* andalso Thm.get_tags t = Thm.get_tags u *)
                                    andalso thms_eq ts us
      fun isprev (name,ths) prev = case Facts.lookup ctx_generic prev name of
                                      NONE => false
                                    | SOME {dynamic=false, thms=ths'} => thms_eq ths ths'
                                    | SOME {dynamic=true, ...} => true (* We don't compare dynamics, we just assume they are not overwritten *)
  in
  Facts.fold_static (fn (name, ths) =>
    if exists (isprev (name, ths)) prev_facts orelse
      not verbose andalso Facts.is_concealed facts name then I
    else cons (name, ths)) facts []
  |> sort_by #1
  end


(* Given a theorem thm, replaces all occurrences of the free vars "fixes" by the free vars "fixed".
   For any hypothesis of thm that is not a fact in the context "ctx", a premise is added to the theorem.
   (Thus, the resulting theorem will be valid in "ctx")

   fixes is a list of (_,n,T) where n is the var name and T the type

   fixed is a list of variable names (types will be the same).
 *)
fun translate_thm ctx fixes fixed thm = 
  let val hyps = Thm.chyps_of thm
      val thm = fold_rev Thm.implies_intr hyps thm
      val idx = Thm.maxidx_of thm + 1
(* val _ = @{print} (1,thm) *)
      val thm = Thm.generalize ([],map #2 fixes) idx thm
(* val _ = @{print} (2,thm,idx,fixes,fixed) *)
      val thm = Thm.instantiate ([],map2 (fn (_,n,T) => fn m => ((Name.clean_index(n,idx),T),Thm.cterm_of ctx (Free(m,T)))) fixes fixed) thm
(* val _ = @{print} (3,thm) *)
      val facts = Proof_Context.facts_of ctx
      fun mk_hypnew hyp =
        let val chyp = Thm.cterm_of ctx hyp
            val hyp_thm = Thm.trivial chyp
            val candidates = Facts.could_unify facts hyp |> map fst
            fun try_cand cand fallback = 
                (* let val hyp = hyp_thm OF [cand]
                    val hyp_concl = Thm.concl_of hyp
                    
                in hyp end *) hyp_thm OF [cand]
                handle THM _ => fallback
        in fold try_cand candidates hyp_thm end
      val prems = take (length hyps) (Thm.prems_of thm)
      val hypsnew = map mk_hypnew prems
(* val _ = @{print} (thm,map (Thm.cterm_of ctx) prems) *)
      val thm = thm OF hypsnew
   in thm end


fun ren_frees [] = I
  | ren_frees pairs =
      let fun substf u =
            case u of Abs(a,T,t) => Abs(a, T, substf t)
                    | t$u' => substf t $ substf u'
                    | Free(n,T) => (case AList.lookup (op=) pairs n of
                                      SOME n' => Free(n',T)
                                    | NONE => u)
                    | _ => u
      in  substf  end;

fun get_fixes ctx =
    let val fixes = Variable.dest_fixes ctx
        val (constr,_) = Variable.constraints_of ctx
    in map (fn (int,ext) => case Vartab.lookup constr (ext,~1) of NONE => error "no constraint" | SOME T => (int,ext,T)) fixes end


fun negate (Const(@{const_name Trueprop},_) $ t) = HOLogic.mk_Trueprop (HOLogic.mk_not t)
  | negate t = raise TERM ("expected boolean proposition",[t])

(* Assumes: goal=X, thm=\<not>Y\<Longrightarrow>X, hyp_thm="Y\<Longrightarrow>A\<^sub>1\<Longrightarrow>\<dots>\<Longrightarrow>A\<^sub>n\<Longrightarrow>X", assms=[A1,\<dots>,A\<^sub>n] *)
fun negation_tac ctx thm hyp_thm assms = 
  (* Goal: X *)
  resolve_tac ctx (@{thms HOL.case_split}) 1
  THEN
  (* Goal: ?P\<Longrightarrow>X, \<not>?P\<Longrightarrow>X  *)
  solve_tac ctx [thm] 2
  THEN  
  (* Goal: Y\<Longrightarrow>X  *)
  resolve_tac ctx [hyp_thm] 1
  THEN
  (* Goal: Y\<Longrightarrow>Y, A1\<Longrightarrow>Y, \<dots>, An\<Longrightarrow>Y  *)
  assume_tac ctx 1
  (* Goal: A1\<Longrightarrow>Y, \<dots>, An\<Longrightarrow>Y  *)
  THEN
  ALLGOALS (fn i => (@{print} (assms,i); resolve_tac ctx [nth assms (i-1)] i))

fun wlog (newassm_name,newassm) (fixes:(binding*string*typ) list) (thesis:term) (assms:(string*thm list)list) int state =
  let val _ = @{print} (Proof.goal state)
      val ctx = Proof.context_of state
      val facts = Proof_Context.facts_of ctx
      (* flat_assms: list of (name,i,t) where t are all assumptions, with i an index to distinguish several propositions in the same fact. (i=0 if there is only one) *)
      val flat_assms = assms |> map (fn (name,thms) => case thms of [th] => [(name,0,Thm.prop_of th)]
                                                                  | _ => map_index (fn (i,thm) => (name,i+1,Thm.prop_of thm)) thms) |> List.concat
      val flat_assms = (Binding.name_of newassm_name,0,newassm) :: flat_assms
      fun idx_name (name,0) = name | idx_name (name,i) = name ^ "_" ^ string_of_int i
      val _ = List.map (fn (name,i,t) => Output.information ("[Wlog] Keeping fact: " ^ idx_name(name,i) ^ ": " ^ (Syntax.string_of_term ctx t))) flat_assms
      val hyp = Logic.list_implies (map #3 flat_assms, thesis)
      val hyp = fold (fn (_,a,T) => fn t => Logic.all_const T $ (Term.absfree (a,T) t)) fixes hyp
      (* val _ = Output.information ("[Wlog] New goal will be:" ^ (Syntax.string_of_term ctx hyp)) *)
      val _ = Output.information ("[Wlog] " ^ (Element.pretty_statement ctx "New goal:" (Thm.assume (Thm.cterm_of ctx hyp)) |> Pretty.string_of))
      val case_names = map (fn (name,i,_) => idx_name(name,i)) flat_assms
      val case_names = Rule_Cases.cases_hyp_names case_names (map (K []) case_names)
      val state = Proof.presume [] [] [((@{binding hypothesis},[case_names]),[(hyp,[])])] state
      val hyp_thm = Proof.the_fact state
      (* val negation_thesis = Logic.mk_implies (negate newassm, thesis) *)

      fun after_qed (_(*ctx*),_) state = 
      let 
          val proven_thm = Proof.the_fact state
          val _ = @{print} (proven_thm)
          val (_,state) = Proof.show true NONE (fn _ => I) [] [] [((Binding.empty,[]),[(thesis,[])])] int state
           val state = Proof.apply (Method.Basic (fn ctx => 
              (Method.SIMPLE_METHOD (negation_tac ctx proven_thm hyp_thm (assms |> map snd |> List.concat)))),
                      Position.no_range) state
              |> Seq.the_result "internal error: negation_tac failed"
          val state = Proof.local_done_proof state
          val let_bindings = Variable.binds_of (Proof.context_of state) |> Vartab.dest
          val state = Proof.next_block state
          val lost_facts = dest_static2 (Proof.context_of state) false [Proof_Context.facts_of (Proof.context_of state)] facts
          val _ = @{print} ("lost_facts",map #1 lost_facts)
          val (fixed,state) = Proof.map_context_result (Proof_Context.add_fixes (map (fn (a,_,T) => (a,SOME T,NoSyn)) fixes)) state
          val rename_fixed = ren_frees (map2 (fn (_,a,_) => fn b => (a,b)) fixes fixed)
          val state = fold (fn (name,(_,t)) => Proof.map_context (Variable.bind_term (name,rename_fixed t))) let_bindings state
          val state = Proof.map_context (Variable.bind_term (("wlog_goal",0),rename_fixed thesis)) state
          val state = fold (fn (name,assm) => fn state => 
                        Proof.assume [] [] [((Binding.name name,[]),map (fn t => (rename_fixed (Thm.prop_of t),[])) assm)] state) assms state
          val ctx = Proof.context_of state
          val state = Proof.note_thmss (map (fn (name,thms) => ((Long_Name.explode name |> split_last |> snd |> Binding.name,[]),[(map (translate_thm ctx fixes fixed) thms, [])])) lost_facts) state
          val state = Proof.assume [] [] [((newassm_name,[]),[(rename_fixed newassm,[])])] state (* Should be last in order to override "this" *)
          (* TODO: define assms to contain all assumptions (carried over and new) *)
      in state end
                            
      val (_,state) = Proof.have true NONE after_qed [] [((@{binding negation},[]),[(negate newassm,[])])] [((Binding.empty,[]),[(thesis,[])])] int state 
  in state end

fun wlog_cmd ((bind,stmt) : Binding.binding * string) (* New assumptions added wlog *)
             (fixes : binding list) (* Variables to be generalized *)
             (goal : string) (* Current goal *)
             (assms : (Facts.ref * Token.src list) list) (* Assumptions to keep *)
             int state =
  let val ctx = Proof.context_of state
      val stmt = Syntax.read_prop ctx stmt                                 
      val assms' = map (fn (fact,_) => (Facts.name_of_ref fact, Proof_Context.get_fact ctx fact)) assms
      val goal' = Syntax.read_prop ctx goal
      val constr = Variable.constraints_of ctx |> #1
      val fixes' = map (fn b => let val internal = Variable.lookup_fixed ctx (Binding.name_of b) |> Option.valOf
                                    val T = Vartab.lookup constr (internal,~1) |> Option.valOf
                                in (b,internal,T) end) fixes
      (* val _ = @{print} assms *)
  in wlog (bind,stmt) fixes' goal' assms' int state end                 

val wlog_parser = (Scan.optional (Parse.binding --| Parse.$$$ ":") Binding.empty -- Parse.prop) -- 
                  (Scan.optional (@{keyword "for"} |-- Scan.repeat Parse.binding) []) --
                  (Scan.optional (@{keyword "shows"} |-- Parse.prop) "?thesis") --
                  (Scan.optional (@{keyword "assumes"} |-- Parse.thms1) [])

val _ =
  Outer_Syntax.command @{command_keyword wlog} "TODO"
    (wlog_parser >> (fn ((((stmt,fixes),goal),assms)) => Toplevel.proof' (wlog_cmd stmt fixes goal assms)));


fun extract_thesis ctx [] [] [(_,[thesis])] = 
  (case Proof_Context.read_propp ctx [[thesis]] |> #1 of
      [[Const ("HOL.Trueprop",_) $ t]] => SOME t
    | _ => NONE)
  | extract_thesis _ _ _ _ = NONE

val _ =
  Outer_Syntax.command @{command_keyword goal} "tests if 'show'ing the given goal will work (i.e., whether 'show' will succeed); also sets ?thesis"
    (Parse_Spec.statement -- Parse_Spec.cond_statement -- Parse.for_fixes >> (fn ((shows, (strict, assumes)), fixes) =>
      Toplevel.proof' (fn int => fn state =>
      (Proof.show_cmd strict NONE (K I) fixes assumes shows int state;
      case extract_thesis (Proof.context_of state) fixes assumes shows of NONE => state
        | SOME t => Proof.map_context (Variable.bind_term (("thesis",0),t)) state
      ))))


end