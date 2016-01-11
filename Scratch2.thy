theory Scratch2
imports Procs_Typed
begin

lemma test: "X = X" by simp
thm test[where X=1]

lemma test2: "X1 = X1" by simp
thm test2
thm test2[where X1=1]

end