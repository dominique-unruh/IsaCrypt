theory Scratch
imports Main 
begin

instantiation nat::finite begin
instance sorry
end

lemma test: "finite (UNIV::nat set)" by (rule finite_UNIV)


end
