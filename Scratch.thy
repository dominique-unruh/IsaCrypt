theory Scratch
imports Main Hoare_Typed
begin

definition "denotation_simp == denotation"
definition "denotation_done == denotation"

lemma enter [cong]:
  assumes "P==P'" and "Q==Q'"
  assumes "denotation_simp c == denotation_done c'"
  shows "hoare {P &m} \<guillemotleft>c\<guillemotright> {Q &m} == hoare {P' &m} \<guillemotleft>c'\<guillemotright> {Q' &m}"
sorry

lemma denot [cong]:
  assumes "denotation_simp c == denotation_done c'"
  shows "denotation c == denotation c'"
sorry

lemma while [simp]: 
  assumes "e=e'"
  and "denotation_simp c == denotation_done c'"
  shows "denotation_simp (Lang_Typed.while e c) \<equiv> denotation_done (Lang_Typed.while e' c')"
sorry

lemma ifte [simp]:
  assumes "e=e'"
  and "denotation_simp c == denotation_done c'"
  and "denotation_simp d == denotation_done d'"
  shows "denotation_simp (Lang_Typed.ifte e c d) == denotation_done (Lang_Typed.ifte e' c' d')"
sorry


lemma seq [simp]:
  assumes "denotation_simp c == denotation_done c'"
  and "denotation_simp d == denotation_done d'"
  shows "denotation_simp (seq c d) == denotation_done (seq c' d')"
sorry


lemma program [simp]:
  assumes "denotation_simp c == denotation_done c'"
  shows "denotation_simp (program c) == denotation_done (program c')"
sorry


lemma comm [simp]:
  "denotation_simp (seq a (seq b c)) = denotation_simp (seq (seq a b) c)"
sorry

lemma finish [simp]: 
  assumes "NO_MATCH (Lang_Typed.while e1 c1) a"
  assumes "NO_MATCH (Lang_Typed.ifte e2 c2 d2) a"
  assumes "NO_MATCH (Lang_Typed.seq c3 d3) a"
  assumes "NO_MATCH (program c4) a"
  shows "denotation_simp a = denotation_done a"
sorry


lemma "denotation PROGRAM[ \<guillemotleft>a\<guillemotright>; \<guillemotleft>b\<guillemotright>; \<guillemotleft>c\<guillemotright> ] == denotation PROGRAM [ \<guillemotleft>a\<guillemotright>; {\<guillemotleft>b\<guillemotright>; \<guillemotleft>c\<guillemotright>}; \<guillemotleft>c\<guillemotright> ]"
  using [[simp_trace_new mode=full]]
apply simp

lemma "hoare {True} while (True) { while (True\<and>False) { \<guillemotleft>a\<guillemotright>; \<guillemotleft>seq b c\<guillemotright> } } {False} "
  using [[simp_trace_new mode=full]]
  apply simp

