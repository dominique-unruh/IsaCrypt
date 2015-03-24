theory Modules2
imports Lang_Typed
begin

typedef MT = "{UNIV::(int*unit,int)procedure set}" sorry
definition "MT_a m = Rep_MT"
definition "MT_map (m::MT) = [[''a'']\<mapsto>MT_a m]"

typedef MT2 = "{UNIV::(MT \<Rightarrow> (bool*unit,bool)procedure) set}" sorry
(* and: all funs parametric *)
typedef MT2_inst = "{UNIV::(bool*unit,bool)procedure set}" sorry

typedef MT3 = "{UNIV::(MT2 \<Rightarrow> (bool*unit,string)procedure) set}" sorry
(* and: all funs parametric *)
typedef MT3_inst = "{UNIV::(bool*unit,string)procedure set}" sorry

