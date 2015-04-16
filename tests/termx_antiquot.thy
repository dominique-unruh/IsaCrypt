(* @SUITE utils *)

theory termx_antiquot
imports Main "../TermX_Antiquot"
begin

ML {*
val x = @{term "xx::int"}
val y = @{term "yy::int"};
val t = @{typ "string"};
val tl = @{typ "int list"};
val l = @{term "[1]::int list"};

val _ = @{assert} (@{termx "(x::int)=?x"} = @{term "x=(xx::int)"});
val _ = @{assert} (@{termx "x=(?x::int)"} = @{term "x=(xx::int)"});
val _ = @{assert} (@{termx "(x::?'x.1)=x"} = @{term "x=(x::int)"});
val _ = @{assert} (@{termx "(x::?'t)=x"} = @{term "x=(x::string)"});
val _ = @{assert} (@{typx "?'t list"} = @{typ "string list"});
val _ = @{assert} (@{termx "[] :: ?'tl" where "?'tl\<Rightarrow>?'t list"} = @{term "[]::int list"});
val _ = @{assert} (@{termx "hd (?l::?'l.1)" where "?'l.1\<Rightarrow>?'a list"} = @{term "hd [1]::int"})
*}

end
