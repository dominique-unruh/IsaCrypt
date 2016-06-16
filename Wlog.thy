theory Wlog
imports Main
keywords "wlog" :: "prf_script" and "dummy" :: "prf_script"
begin

declare[[ML_exception_trace]]

ML Term_Subst.generalize
ML {* Name.clean_index ("aa__", 0) *}

ML {*
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
                                    | SOME (true,ths') => thms_eq ths ths'
                                    | SOME (false,_) => true (* We don't compare dynamics, we just assume they are not overwritten *)
  in
  Facts.fold_static (fn (name, ths) =>
    if exists (isprev (name, ths)) prev_facts orelse
      not verbose andalso Facts.is_concealed facts name then I
    else cons (name, ths)) facts []
  |> sort_by #1
  end
*}

ML {*
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
            val candidates = Facts.could_unify facts hyp
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
*}

ML {*
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
*}

ML {*
fun get_fixes ctx =
    let val fixes = Variable.dest_fixes ctx
        val (constr,_) = Variable.constraints_of ctx
    in map (fn (int,ext) => case Vartab.lookup constr (ext,~1) of NONE => error "no constraint" | SOME T => (int,ext,T)) fixes end
*}

ML Assumption.presume_export

lemma x[case_names acase[x y z]]: "a \<Longrightarrow> b \<Longrightarrow> xxx" sorry
lemma "xxx" apply (cases rule:x) print_cases oops
ML Rule_Cases.cases_hyp_names

ML {*
fun wlog (newassm_name,newassm) (fixes:(binding*string*typ) list) (thesis:term) (assms:(string*thm list)list) int state =
  let val _ = @{print} (Proof.goal state)
      val ctx = Proof.context_of state
      val facts = Proof_Context.facts_of ctx
      (* flat_assms: list of (name,i,t) where t are all assumptions, with i an index to distinguish several propositions in the same fact. (i=0 if there is only one) *)
      val flat_assms = assms |> map (fn (name,thms) => case thms of [th] => [(name,0,Thm.prop_of th)]
                                                                  | _ => map_index (fn (i,thm) => (name,i+1,Thm.prop_of thm)) thms) |> List.concat
      val flat_assms = ("new_assm",0,newassm) :: flat_assms
      fun idx_name (name,0) = name | idx_name (name,i) = name ^ "_" ^ string_of_int i
      val _ = List.map (fn (name,i,t) => Output.information ("[Wlog] Assumption " ^ idx_name(name,i) ^ ": " ^ (Syntax.string_of_term ctx t))) flat_assms
      val hyp = Logic.list_implies (map #3 flat_assms, thesis)
      val hyp = fold (fn (_,a,T) => fn t => Logic.all_const T $ (Term.absfree (a,T) t)) fixes hyp
      val _ = Output.information ("[Wlog] New goal will be: " ^ (Syntax.string_of_term ctx hyp))
      val case_names = map (fn (name,i,_) => idx_name(name,i)) flat_assms
      val case_names = Rule_Cases.cases_hyp_names case_names (map (K []) case_names)
      val state = Proof.presume [] [] [((@{binding hypothesis},[case_names]),[(hyp,[])])] state

      fun after_qed (_(*ctx*),_) state = 
      let val let_bindings = Variable.binds_of (Proof.context_of state) |> Vartab.dest
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
          val state = Proof.assume [] [] [((newassm_name,[]),[(rename_fixed newassm,[])])] state (* Should be last to override "this" *)
          (* TODO: define assms to contain all assumptions (carried over and new) *)
      in state end

      val (_,state) = Proof.show true NONE after_qed [] [] [(Thm.empty_binding,[(thesis,[])])] int state
      (* val state = Proof.local_skip_proof int state *)
  in state end
*}

ML {*
fun wlog_cmd ((bind,stmt) : Binding.binding * string) (* New assumptions added wlog *)
             (fixes : binding list) (* Variables to be generalized *)
             (goal : string) (* Current goal *)
             (assms : (Facts.ref * Token.src list) list) (* Assumptions to keep *)
             int state =
  let val ctx = Proof.context_of state
(*       val (bind,stmt) = case error "xxx" of
                            [((bind,[]),[(stmt,[])])] => 
                              let val ctx = Proof.context_of state
                                  val stmt = Syntax.read_prop ctx stmt
                              in (bind,stmt) end
                          | _ => error "wlog: some unsupported case -> add proper error message" *)
      val stmt = Syntax.read_prop ctx stmt                                 
      val assms' = map (fn (fact,_) => (Facts.name_of_ref fact, Proof_Context.get_fact ctx fact)) assms
      val goal' = Syntax.read_prop ctx goal
      val constr = Variable.constraints_of ctx |> #1
      val fixes' = map (fn b => let val SOME internal = Variable.lookup_fixed ctx (Binding.name_of b)
                                    val SOME T = Vartab.lookup constr (internal,~1)
                                in (b,internal,T) end) fixes
      val _ = @{print} assms
  in wlog (bind,stmt) fixes' goal' assms' int state end                 

val wlog_parser = (Scan.optional (Parse.binding --| Parse.$$$ ":") Binding.empty -- Parse.prop) -- 
                  (Scan.optional (@{keyword "for"} |-- Scan.repeat Parse.binding) []) --
                  (@{keyword "shows"} |-- Parse.prop) --
                  (@{keyword "assumes"} |-- Parse.xthms1)

val _ =
  Outer_Syntax.command @{command_keyword wlog} "TODO"
    (wlog_parser >> (fn ((((stmt,fixes),goal),assms)) => Toplevel.proof' (wlog_cmd stmt fixes goal assms)));
*}

ML {*

val _ =
  Outer_Syntax.command @{command_keyword dummy} "TODO"
    (Scan.succeed () >> (fn _ => Toplevel.proof (fn state => (@{print} (state  |> Proof.the_facts ); state))));
*}

lemma
  fixes a b :: nat
  assumes bla: "True"
  assumes neq: "a \<noteq> b"
  shows "a+b \<ge> 1"
proof -
  have neq2: "a>b\<or>b>a" using neq bla by auto 
  have comm: "1 \<le> a + b \<Longrightarrow> 1 \<le> b + a" for a b :: nat by auto

  ML_prf {* val ctx1 = @{context} *}
  ML_prf {* val neq2 = @{thm neq2} *}

  let ?a = a

  have test[]: "\<And>a. b \<noteq> a \<Longrightarrow> a \<noteq> b \<Longrightarrow> 1 \<le> a + b" sorry
  (* have "1 \<le> a+b" proof (cases rule:test) print_cases case 2  *)

have hyptmp[case_names new_assm neq]: "b \<noteq> a \<Longrightarrow> a \<noteq> b \<Longrightarrow> 1 \<le> a + b" for a sorry

consider "a=a" | "b=b" sorry
note c = this
(* have "1 \<le> a + b " proof (cases "True") print_cases case True show ?thesis *)

  wlog neq3: "b\<noteq>a" for a shows "a+b\<ge>(1::nat)" assumes neq
  proof (cases rule:hypothesis[where a=a]) print_cases
    case neq show ?case using assms(2) by blast 
    case new_assm show ?case using assms(2) by blast 
  qed

  have aux: "P \<Longrightarrow> (P \<Longrightarrow> Q) \<Longrightarrow> Q" for P Q by metis

  ML_prf {* val ctx2 = @{context} *}
  wlog geq: "a > b" for a b shows ?thesis assumes neq3
  proof (cases "a>b")
  case True show ?thesis using True hypothesis by blast
  next case False show ?thesis proof (rule aux, cases rule:hypothesis[of a b])
    case new_assm show ?case using False neq2 by blast 
    next case neq3 show ?case using neq2 by auto
    next assume "1 \<le> b + a" then show "1 \<le> a + b" by linarith 
    qed
  qed

  note assms = neq neq3

  have "b<a\<or>a<b" by (simp add: geq)

 (* apply (tactic \<open>resolve_tac @{context} [neq2'] 1\<close>) using assms by auto *)

  wlog tmp: "a=a" for a b shows ?thesis assumes geq 
    using hypothesis neq geq by metis

  from geq have "a \<ge> 1" by auto

  then show "1 \<le> a + b" by auto
qed
