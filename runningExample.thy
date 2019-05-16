theory runningExample
  imports TTC_Calculus

begin

definition T1:: PLTL_formula  
  where "T1 = \<box>( (V ''a'') .\<longrightarrow> ( \<circle>(V ''b'') .\<and> \<circle>(.\<not>(V ''a'')) .\<and> \<circle>(.\<not>(V ''c'')) .\<and> \<circle>(.\<not>(V ''d'')) ) ) "
definition T2:: PLTL_formula  
  where "T2 = \<box>( (V ''b'') .\<longrightarrow> ( (\<circle>(V ''b'') .\<and> \<circle>(.\<not>(V ''a'')) .\<and> \<circle>(.\<not>(V ''c'')) .\<and> \<circle>(.\<not>(V ''d'')))
                                  .\<or>  (\<circle>(V ''c'') .\<and> \<circle>(.\<not>(V ''a'')) .\<and> \<circle>(.\<not>(V ''b'')) .\<and> \<circle>(.\<not>(V ''d''))) )  )"
definition T3:: PLTL_formula  
  where "T3 = \<box>( (V ''c'') .\<longrightarrow> ( \<circle>(V ''b'') .\<and> \<circle>(.\<not>(V ''a'')) .\<and> \<circle>(.\<not>(V ''c'')) .\<and> \<circle>(.\<not>(V ''d'')) ) )"
definition T4:: PLTL_formula  
  where "T4 = \<box>( (V ''d'') .\<longrightarrow> ( \<circle>(V ''a'') .\<and> \<circle>(.\<not>(V ''b'')) .\<and> \<circle>(.\<not>(V ''c'')) .\<and> \<circle>(.\<not>(V ''d'')) ) )"

definition Init:: PLTL_formula  
  where "Init = ((V ''a'') .\<and> .\<not>(V ''b'') .\<and> .\<not>(V ''c'') .\<and> .\<not>(V ''d''))"

definition TR where "TR = [T1, T2, T3, T4]"

definition S where "S = TR @ [Init]"

end
