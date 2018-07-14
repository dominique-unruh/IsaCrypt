theory Do_Notation_Monads
  imports Do_Notation CryptHOL
begin

ML {* val dummify = Do_Notation.dummify *}

local_setup {*
Do_Notation.add_monad @{binding list} 
  {bind = dummify @{context} @{term "List.bind"},
   return = dummify @{context} @{term "%x. [x]"}
  }
*}

local_setup {*
Do_Notation.add_monad @{binding spmf} 
  {bind = dummify @{context} @{term bind_spmf},
   return = dummify @{context} @{term return_spmf}}
*}


value "do Do_Notation_Monads.list { a<-[1::int,2,3]; b<-[4,5,6]; return a*b }"
value "do spmf { a<-xxx; b<-yyy; return a*b }"
