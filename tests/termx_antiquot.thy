(* @SUITE utils *)

theory termx_antiquot
imports Main "../TermX_Antiquot"
begin

ML {*
val x = @{term "xx::int"}
val y = @{term "yy::int"};
val t = @{typ "string"};
val tl = @{typ "int list"};

@{assert} (@{termx "(x::int)=?x"} = @{term "x=(xx::int)"});
@{assert} (@{termx "x=(?x::int)"} = @{term "x=(xx::int)"});
@{assert} (@{termx "(x::?'x.1)=x"} = @{term "x=(x::int)"});
@{assert} (@{termx "(x::?'t)=x"} = @{term "x=(x::string)"});
@{assert} (@{typx "?'t list"} = @{typ "string list"});
@{assert} (@{termx "[] :: ?'tl" where "?'tl\<Rightarrow>?'t list"} = @{term "[]::int list"});
*}

end
