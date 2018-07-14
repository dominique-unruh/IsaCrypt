theory Do_Notation
  imports Main Monad_Syntax 
begin

nonterminal monad_id
syntax
  "_do_block_named" :: "monad_id \<Rightarrow> do_binds \<Rightarrow> 'a" ("do _ {//(2  _)//}" [12] 62)
  "_do_return" :: "'a \<Rightarrow> do_binds" ("return _" 13)
  "_bind_do_named" :: "monad_id \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c"
  "_return_do_named" :: "monad_id \<Rightarrow> 'a \<Rightarrow> 'b"
  "" :: "id \<Rightarrow> monad_id" ("_")
  "" :: "longid \<Rightarrow> monad_id" ("_")

translations
  "_do_block_named N (_do_cons (_do_then t) (_do_final e))"
    \<rightleftharpoons> "_bind_do_named N t (\<lambda>_. e)"
  "_do_block_named N (_do_cons (_do_bind p t) (_do_final e))"
    \<rightleftharpoons> "_bind_do_named N t (\<lambda>p. e)"
  "_do_block_named N (_do_cons (_do_let p t) bs)"
    \<rightleftharpoons> "let p = t in _do_block_named N bs"
  "_do_block_named N (_do_cons b (_do_cons c cs))"
    \<rightharpoonup> "_do_block_named N (_do_cons b (_do_final (_do_block_named N (_do_cons c cs))))"
  "_do_block_named N (_do_cons b (_do_return x))"
    \<rightharpoonup> "_do_block_named N (_do_cons b (_do_final (_do_block_named N (_do_return x))))"
(*   "_do_cons (_do_let p t) (_do_final s)"
    \<rightleftharpoons> "_do_final (let p = t in s)" *)
  "_do_block_named N (_do_final e)" \<rightharpoonup> "e"
  (* "(m \<then> n)" \<rightharpoonup> "(m \<bind> (\<lambda>_. n))" *)
  "_do_block_named N (_do_return x)" \<rightharpoonup> "_return_do_named N x"

ML_file "do_notation.ML"

parse_translation \<open> (*TODO: name does not have a position constraint, thus: no markup in parsed term *)
  [("_bind_do_named", fn ctx => fn [name,m,f] => (Do_Notation.lookup_monad_term ctx (@{print}name) |> snd |> #bind) $ m $ f),
   ("_return_do_named", fn ctx => fn [name,x] => (Do_Notation.lookup_monad_term ctx name |> snd |> #return) $ x)]
\<close>

end