theory Multi_Monad
  imports CryptHOL
  keywords "monad" :: thy_goal
begin


ML_file "multi_monad.ML"

monad list "%x. [x]" List.bind by simp
monad option "Some" Option.bind by simp

ML {*
 Multi_Monad.print_functors @{context}
*}

functor  llmap