theory Scratch
imports "~~/src/HOL/Proofs/Lambda/InductTermi"
begin

lemma badlemma: "False" sorry
class noneq = assumes neq: "a\<noteq>b"
instantiation nat :: noneq begin
instance apply intro_classes
  using badlemma apply auto done
end
lemma bad2: "(1::nat)\<noteq>1"
  by (rule neq)
thm_deps bad2
unused_thms
ML Thm_Deps.unused_thms
inductive betasub :: "[dB, dB] => bool"  (infixl "\<longrightarrow>\<^sub>\<beta>" 50)
  where
     "Abs s \<degree> t \<longrightarrow>\<^sub>\<beta> s[t/0]"
  | "s \<longrightarrow>\<^sub>\<beta> t ==> s \<degree> u \<longrightarrow>\<^sub>\<beta> t \<degree> u"
  | "s \<longrightarrow>\<^sub>\<beta> t ==> u \<degree> s \<longrightarrow>\<^sub>\<beta> u \<degree> t"
  | "s \<longrightarrow>\<^sub>\<beta> t ==> Abs s \<longrightarrow>\<^sub>\<beta> Abs t"
  | "App f g \<longrightarrow>\<^sub>\<beta> f"
term beta

lemma "IT x \<Longrightarrow> x=App f g \<Longrightarrow> IT f"
  apply (induct arbitrary: f g rule:IT.cases)
  apply clarify

lemma bla: "undefined=2 \<and> 2=3" 
  apply rule
  apply (tactic {* cheat_tac_annot (SOME "hello there") @{here} 1 *})
  sorry

ML {*
print_annotated_oracles @{context} @{thm bla};
*}


