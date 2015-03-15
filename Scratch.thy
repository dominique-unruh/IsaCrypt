theory Scratch imports Main begin


locale test =
  fixes a :: 'n
begin

definition "b == undefined a"

thm b_def

end

thm test.b_def


ML {*
val thm_ref = Unsynchronized.ref @{thm refl};

fun def lthy = 
let val ((n1,(n2,thm)), lthy') =
  Local_Theory.define ((@{binding test},NoSyn), ((@{binding test_def},[]), @{term 123})) lthy
val _ = thm_ref := (Proof_Context.export lthy lthy' [thm] |> hd)
val _ = @{print} (n1,n2,thm)
in lthy' end;

fun def2 lthy' = let
val ((n3,thm'),lthy'') = Local_Theory.note ((@{binding test_def2},[]), [!thm_ref]) lthy'
val _ = @{print} (n3,thm')
in lthy'' end
*}

local_setup "def"
ML {* !thm_ref *}
local_setup "def2"


thm test_def
thm test_def2
