theory Multi_Monad
  imports CryptHOL
  keywords "monad" :: thy_goal
begin


ML_file "multi_monad.ML"


monad list: "_ list" "%x. [x::'c]" List.bind 
proof -
  show "[x] \<bind> f = f x" by auto
  show "m \<bind> (\<lambda>x. [x]) = m" 
    unfolding List.bind_def by auto 
  show "(m \<bind> f) \<bind> g = m \<bind> (\<lambda>x. f x \<bind> g)"
    unfolding List.bind_def 
    by (induction m, auto)
qed

monad option: "_option" "Some" Option.bind 
  by auto

ML {*
 Multi_Monad.print_functors @{context}
*}

monad pmf: "_pmf" return_pmf bind_pmf
    apply (rule bind_return_pmf)
   apply (rule bind_return_pmf')
  by (rule bind_assoc_pmf)

(* typedef 'b SPMF = "UNIV :: 'b spmf set" by simp
setup_lifting type_definition_SPMF
lift_definition return_SPMF :: "'b \<Rightarrow> 'b SPMF" is return_spmf .
lift_definition bind_SPMF :: "'b SPMF \<Rightarrow> ('b\<Rightarrow>'c SPMF) \<Rightarrow> 'c SPMF" is bind_spmf . *)

monad spmf: "_ spmf" return_spmf bind_spmf by auto

(* typedef 'a total = "UNIV :: 'a set" 
  morphisms Rep_total return_total 
  ..
setup_lifting type_definition_total
lift_definition bind_total :: "'a total \<Rightarrow> ('a \<Rightarrow> 'b total) \<Rightarrow> 'b total" is "%m f. f m" . *)

find_consts "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"
monad total: _ id Let by auto

(* lift_definition pmf_to_SPMF :: "'a pmf \<Rightarrow> 'a SPMF" is spmf_of_pmf . *)
lemma "spmf_of_pmf (return_pmf x) = return_spmf x" by auto
lemma "spmf_of_pmf (bind_pmf m f) = bind_spmf (spmf_of_pmf m) (\<lambda>x. spmf_of_pmf (f x))" 
  apply simp using spmf_of_pmf_bind by blast 

lemma "return_pmf (id x) = return_pmf x" apply transfer by auto
lemma "return_pmf (Let m f) = bind_pmf (return_pmf m) (\<lambda>x. return_pmf (f x))" 
  by (simp add: bind_return_pmf) 

lift_definition option_to_spmf :: "'a option \<Rightarrow> 'a spmf" is "return_pmf :: 'a option \<Rightarrow> _" .
lemma "option_to_spmf (Some x) = return_spmf x" apply transfer by auto
lemma "option_to_spmf (Option.bind m f) = bind_spmf (option_to_spmf m) (\<lambda>x. option_to_spmf (f x))" 
  apply transfer
  by (metis bind.bind_lunit bind_spmf_cong return_bind_spmf return_pmf_bind_option) 

(* lift_definition total_to_option :: "'a total \<Rightarrow> 'a option" is Some . *)
lemma "Some (id x) = Some x" apply transfer by simp
lemma "Some (Let m f) = Option.bind (Some m) (\<lambda>x. Some (f x))" 
  apply transfer by simp 

lemma "spmf_of_pmf (return_pmf m) = option_to_spmf (Some m)"
  apply transfer by simp

typedef ('a,'b) state_spmf = "UNIV :: ('b\<Rightarrow>('a*'b) spmf) set" ..
setup_lifting type_definition_state_spmf
lift_definition return_state_spmf :: "'a \<Rightarrow> ('a,'b) state_spmf" is "\<lambda>x s. return_spmf (x,s)" .
lift_definition bind_state_spmf :: "('a,'s) state_spmf \<Rightarrow> ('a \<Rightarrow> ('b,'s) state_spmf) \<Rightarrow> ('b,'s) state_spmf" 
  is "\<lambda>(m::'s\<Rightarrow>('a*'s) spmf) (f::('a\<Rightarrow>'s\<Rightarrow>('b*'s) spmf)) (s::'s). bind_spmf (m s) (%(x,s). f x s)" .

declare[[ML_exception_trace]]

monad state: "(_,'s) state_spmf" return_state_spmf bind_state_spmf
    apply transfer apply simp
   apply transfer apply (rule ext) unfolding case_prod_beta apply simp
  apply transfer apply (rule ext) unfolding case_prod_beta by simp

lift_definition add_state :: "'a spmf \<Rightarrow> ('a,'s) state_spmf" is "%m s. (bind_spmf m (%x. return_spmf (x,s)))" .
lemma "add_state (return_spmf x) = return_state_spmf x" apply transfer by simp
lemma "add_state (bind_spmf m f) = bind_state_spmf (add_state m) (\<lambda>x. add_state (f x))" 
  apply transfer by simp 

