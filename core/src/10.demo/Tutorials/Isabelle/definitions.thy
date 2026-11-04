

theory definitions

imports types
begin
definition intify::"nat \<Rightarrow> int" where
"intify n = int n"

fun double::"nat \<Rightarrow> nat"where
"double (Suc n) = 2+ double n" |
"double n = 0"

function doublef::"nat \<Rightarrow> nat"where
"doublef 0 = 0" |
"doublef (Suc n) = 2+ doublef n"
  using not0_implies_Suc by auto
termination
  using "termination" by auto

primrec doublep::"nat \<Rightarrow> nat" where
"doublep 0 = 0" |
"doublep (Suc n) = 2+ doublep n"

fixrec lzip :: "'a llist \<rightarrow> 'b llist \<rightarrow> ('a \<times> 'b)llist"where 
"lzip\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>(lCons\<cdot>y\<cdot>ys) = lCons\<cdot>(x,y)\<cdot>(lzip\<cdot>xs\<cdot>ys)"

end