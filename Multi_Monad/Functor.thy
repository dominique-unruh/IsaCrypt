theory Functor
  imports Main
begin

typedecl 'a FUNCTOR

ML_file "functor.ML"

consts MAP :: "('a\<Rightarrow>'b) \<Rightarrow> ('a FUNCTOR=>'b FUNCTOR)"

setup {*
  Functor.add_template_global {
    name = @{binding functor},
    operations = [@{term MAP}] |> map dest_Const,
    laws = [("map_id",@{prop "MAP id = id"}),("map_comp",@{prop "\<And>f g. MAP (g o f) = MAP g o MAP f"})]
  }
*}

consts
  RETURN :: "'a \<Rightarrow> 'a FUNCTOR"
  BIND :: "'a FUNCTOR \<Rightarrow> ('a \<Rightarrow> 'b FUNCTOR) \<Rightarrow> 'b FUNCTOR"

setup {*
  Functor.add_template_global {
    name = @{binding monad},
    operations = [@{term RETURN},@{term BIND}] |> map dest_Const,
    laws = [("return_bind", @{prop "\<And>v f. BIND (RETURN v) f = f v"}),
            ("bind_return", @{prop "\<And>m. BIND m RETURN = m"}),
            ("bind_assoc", @{prop "\<And>m f g. BIND (BIND m f) g = BIND m (\<lambda>x. BIND (f x) g)"})]
  }
*}

ML {*
  Functor.print_templates @{context}
*}

end
