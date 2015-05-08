theory Universe
imports Main BNF_Cardinal_Order_Relation
begin

(* For proving instances of types declared with 
  "datatype" (not "datatype_new"), see, e.g., "char"

  For proving instances of types declared with 
  "typedef", see, e.g., "ell1"
*)
                                       
definition "powertower t == \<forall>n. \<exists>i. inj_on i (Pow (t n)) \<and> i ` (Pow (t n)) \<subseteq> t (Suc n)"

typedecl val
axiomatization where
  powertower_nat: "\<exists>t n (i::nat\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n" 

instantiation val :: equal begin
definition "equal_val (v::val) w = (v=w)"
instance apply intro_classes by (simp add: equal_val_def)
end

class prog_type = default +
  assumes small_cardinal: "\<exists>t n (i::'a\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n"

definition embedding :: "'a::prog_type \<Rightarrow> val" where
  "embedding == (SOME f::'a\<Rightarrow>val. inj f)"

lemma embedding_inv [simp]: "(embedding x = embedding y) = (x = y)"
  apply (rule inj_eq) unfolding embedding_def
  apply (rule someI_ex[of "\<lambda>f. inj f"]) using small_cardinal
  by auto

lemma embedding_inv': "inv embedding (embedding x) = x"
  by (metis embedding_inv f_inv_into_f range_eqI)
  

instantiation "nat" :: prog_type begin
instance apply intro_classes using powertower_nat by auto
end

lemma prog_type_classI':
  assumes "\<exists>f::'a\<Rightarrow>'b::prog_type. inj f"
  shows "\<exists>t n (i::'a\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n"
proof -
  obtain t n and i::"'b\<Rightarrow>val" where "powertower t" and "inj i" and "range i \<subseteq> t n"
    using small_cardinal by auto
  obtain f::"'a\<Rightarrow>'b" where "inj f" using assms by auto
  show "\<exists>t n (i::'a\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n"
    apply (rule exI[where x=t])
    apply (rule exI[where x=n])
    apply (rule exI[where x="i o f"], auto) 
    apply (fact `powertower t`)
    apply (metis (mono_tags, hide_lams) `inj i` `inj f` comp_apply injI inj_eq)
    by (metis `range i \<subseteq> t n` range_eqI subsetCE)
qed 

lemma prog_type_classI:
  assumes "\<exists>f::'a\<Rightarrow>'b::prog_type. inj f"
  shows "OFCLASS('a, prog_type_class)"
apply intro_classes using assms by (rule prog_type_classI')

instantiation set :: (prog_type) prog_type begin
instance proof
  obtain t n and i::"'a\<Rightarrow>val" where pow: "powertower t" and "inj i" and irng: "range i \<subseteq> t n"
    using small_cardinal by auto
  from pow obtain i2::"val set\<Rightarrow>val" where i2inj: "inj_on i2 (Pow (t n))" and i2rng: "i2 ` Pow(t n) \<subseteq> t (Suc n)"
    unfolding powertower_def by blast
  def i3 == "\<lambda>s. i2 (i ` s)"
  have "inj i3"
  proof (rule injI, unfold i3_def)
    fix x y 
    from `inj i` have i: "i ` x = i ` y \<Longrightarrow> x = y"
      by (metis inj_image_eq_iff)
    show "i2 (i ` x) = i2 (i ` y) \<Longrightarrow> x = y"
      apply (rule i)
      apply (subst inj_on_eq_iff[symmetric, where f=i2 and A="Pow(t n)"])
      using i2inj apply simp_all
      by (metis Pow_UNIV Pow_iff image_Pow_surj image_iff irng subset_UNIV subset_trans)+
  qed
  have i3rng: "range i3 \<subseteq> t (Suc n)"
  proof (unfold i3_def, auto)
    fix s
    have "i ` s \<in> Pow (t n)" using irng by auto
    hence "i2 (i ` s) \<in> i2 ` (Pow (t n))" by auto
    with i2rng show "i2 (i ` s) \<in> t (Suc n)" by auto
  qed
  show "\<exists>t n (i::'a set\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n"
    apply (rule exI)+
    apply (rule conjI, fact pow)
    apply (rule conjI, fact `inj i3`)
    by (fact i3rng)    
qed
end

instantiation bool :: prog_type begin
instance apply (rule prog_type_classI, rule exI[where x="\<lambda>b. if b then 0 else Suc 0"])
  apply (rule injI)
  by (case_tac x, case_tac y, auto)
end

lemma ordered_cardinals: "(\<exists>i::'a\<Rightarrow>'b. inj i) \<or> (\<exists>j::'b\<Rightarrow>'a. inj j)"
proof -
  have leq: "ordLeq2 (card_of (Inl ` UNIV :: ('a+'b)set)) (card_of (Inr ` UNIV :: ('a+'b)set)) \<or>
        ordLeq2 (card_of (Inr ` UNIV :: ('a+'b)set)) (card_of (Inl ` UNIV :: ('a+'b)set))"
        by (rule ordLeq_total, rule card_of_Well_order, rule card_of_Well_order)
  show ?thesis proof (rule leq[THEN disjE], fold card_of_ordLeq)
    assume "\<exists>f::'a+'b \<Rightarrow> 'a+'b. inj_on f (range Inl) \<and> f ` range Inl \<subseteq> range Inr"
    then obtain f::"'a+'b \<Rightarrow> 'a+'b" where finj: "inj_on f (range Inl)" and frng: "f ` range Inl \<subseteq> range Inr" by auto
    def i == "\<lambda>x. case f (Inl x) of Inr y \<Rightarrow> y"
    have "inj i" proof (rule injI, unfold i_def) 
      fix x y assume eq:"(case f (Inl x) of Inr y \<Rightarrow> y) = (case f (Inl y) of Inr y \<Rightarrow> y)"
      from frng obtain x' where x': "f (Inl x) = Inr x'" by blast
      from frng obtain y' where y': "f (Inl y) = Inr y'" by blast
      from eq have "f (Inl x) = f (Inl y)" unfolding x' y' by simp
      with finj have "Inl x = Inl y" unfolding inj_on_def by simp
      thus "x = y" by auto
    qed
    thus ?thesis by auto
  next
    assume "\<exists>f::'a+'b \<Rightarrow> 'a+'b. inj_on f (range Inr) \<and> f ` range Inr \<subseteq> range Inl"
    then obtain f::"'a+'b \<Rightarrow> 'a+'b" where finj: "inj_on f (range Inr)" and frng: "f ` range Inr \<subseteq> range Inl" by auto
    def j == "\<lambda>x. case f (Inr x) of Inl y \<Rightarrow> y"
    have "inj j" proof (rule injI, unfold j_def) 
      fix x y assume eq:"(case f (Inr x) of Inl y \<Rightarrow> y) = (case f (Inr y) of Inl y \<Rightarrow> y)"
      from frng obtain x' where x': "f (Inr x) = Inl x'" by blast
      from frng obtain y' where y': "f (Inr y) = Inl y'" by blast
      from eq have "f (Inr x) = f (Inr y)" unfolding x' y' by simp
      with finj have "Inr x = Inr y" unfolding inj_on_def by simp
      thus "x = y" by auto
    qed
    thus ?thesis by auto
  qed
qed

instantiation sum :: (prog_type,prog_type) prog_type begin
instance proof (intro_classes, cases "\<exists>i::'a\<Rightarrow>'b. inj i")
case True
  then obtain i::"'a\<Rightarrow>'b" where "inj i" by auto
  def i2 == "\<lambda>x::'a+'b. case x of Inl a \<Rightarrow> {{i a}} | Inr b \<Rightarrow> {{b},{}}"
  have "inj i2" apply (rule injI) unfolding i2_def 
    apply (case_tac x, case_tac y, auto)
    apply (metis `inj i` inj_eq)
    by (case_tac y, auto)
  hence "\<exists>f::'a+'b\<Rightarrow>'b set set. inj f"
    by (rule exI[of _ i2])
  thus "\<exists>t n (i::'a+'b\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n"
    by (rule prog_type_classI')
next 
case False
  with ordered_cardinals obtain i::"'b\<Rightarrow>'a" where "inj i" by auto
  def i2 == "\<lambda>x::'a+'b. case x of Inl a \<Rightarrow> {{a},{}} | Inr b \<Rightarrow> {{i b}}"
  have "inj i2" apply (rule injI) unfolding i2_def 
    apply (case_tac x, case_tac y, auto)
    apply (case_tac y, auto)
    by (metis `inj i` inj_eq)
  hence "\<exists>f::'a+'b\<Rightarrow>'a set set. inj f"
    by (rule exI[of _ i2])
  thus "\<exists>t n (i::'a+'b\<Rightarrow>val). powertower t \<and> inj i \<and> range i \<subseteq> t n"
    by (rule prog_type_classI')
qed
end

instantiation prod :: (prog_type,prog_type) prog_type begin
instance apply (rule prog_type_classI)
  apply (rule exI[where x="\<lambda>(x::'a,y::'b). {Inl x,Inr y}"])
  apply (rule injI)
  by (case_tac x, case_tac y, auto)
end


instantiation "fun" :: (prog_type,prog_type)prog_type begin
instance
  apply (rule prog_type_classI)
  apply (rule exI[where x="\<lambda>f. {(x,f x)| x. True}"])
  by (rule injI, auto)
end

instantiation list :: (prog_type) prog_type begin
instance apply (rule prog_type_classI, rule exI[where x="\<lambda>l. (length l, nth l)"])
  by (rule injI, metis nth_equalityI old.prod.inject)
end

lemma OFCLASS_prog_type_typedef:
  fixes Rep::"'a\<Rightarrow>_::prog_type"
  assumes "\<And>x y. (Rep x = Rep y) = (x = y)" 
  shows "OFCLASS('a,prog_type_class)"
apply (rule prog_type_classI, rule exI[of _ Rep])
using assms unfolding inj_on_def by auto

(*instantiation int::prog_type begin
instance by (fact OFCLASS_prog_type_typedef[OF Rep_int_inject]) end *)

(*
instantiation rat::prog_type begin
instance by (fact OFCLASS_prog_type_typedef[OF Rep_rat_inject]) end
  
instantiation real::prog_type begin
instance by (fact OFCLASS_prog_type_typedef[OF Rep_real_inject]) end
*)

subsection {* Automatically instantiate new types (defined via typedef) *}

ML {*
fun instantiate_prog_type tycon thy =
let val arity = Sign.arity_number thy tycon
    val sorts = replicate arity @{sort "prog_type"}
    val vs = Name.invent_names Name.context "'a" sorts
    val Rep_inject = 
      case Typedef.get_info_global thy tycon of
        [info] => #Rep_inject (snd info)
      | [] => error (tycon^" not defined by typedef")
      | _ => error ("Typedef.get_info_global thy \""^tycon^"\" returns several items")
    val OFCLASS_prog_type_typedef = Global_Theory.get_thm thy "Universe.OFCLASS_prog_type_typedef"
    val OFCLASS_thm = OFCLASS_prog_type_typedef OF [Rep_inject]
      handle THM _ => error ("Instance proof failed (when instantiating thm OFCLASS_prog_type_typedef).\nProbably the representing set of the type '"^tycon^"' is not of sort prog_type.")
    val thy = Class.instantiation ([tycon],vs,@{sort "prog_type"}) thy
    val thy = Class.prove_instantiation_exit (fn _ => rtac OFCLASS_thm 1) thy
      handle THM _ => error ("Instance proof failed.")
in
thy
end;

fun try_instantiate_prog_type tycon thy =
  instantiate_prog_type tycon thy
  handle ERROR _ => (tracing ("Did not instantiate "^tycon^" :: prog_type"); thy);
*}


setup {* Typedef.interpretation (Local_Theory.background_theory o try_instantiate_prog_type) *}

subsection {* Instantiation for types not handled by automated mechanism *}

(*instantiation option :: (prog_type)prog_type begin
instance apply (rule prog_type_classI, rule exI[where x="\<lambda>x. case x of Some x \<Rightarrow> Inl x | None \<Rightarrow> Inr ()"])
proof (rule injI) (* Sledgehammer proof *)
  fix x :: "'a option" and y :: "'a option"
  assume a1: "(case x of None \<Rightarrow> Inr () | Some f \<Rightarrow> Inl f) = (case y of None \<Rightarrow> Inr () | Some f \<Rightarrow> Inl f)"
  then obtain esk3\<^sub>1 :: "'a option \<Rightarrow> 'a" where "y = x \<or> None = x \<or> y = None" by (metis option.case(2) option.exhaust sum.sel(1))
  thus "x = y" using a1 by (metis (no_types) Inr_not_Inl option.case_eq_if)
qed
end*)

(*instantiation distr::(prog_type)prog_type begin
instance by (fact OFCLASS_prog_type_typedef[OF Rep_distr_inject]) end*)

(*instantiation nibble::prog_type begin
instance by (fact OFCLASS_prog_type_typedef[OF Rep_nibble_inject]) end*)

(*instantiation char :: prog_type begin
instance apply (rule prog_type_classI, rule exI[where x=Rep_char])
  by (metis Rep_char_inverse injI)
end*)


end
