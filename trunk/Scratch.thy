theory Scratch
imports Main Extended_Sorry
begin

instantiation nat::finite begin
instance SORRY
end

lemma test: "finite (UNIV::nat set)" by (rule finite_UNIV)

end
