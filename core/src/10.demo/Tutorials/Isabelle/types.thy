
theory types

imports documentation
begin

default_sort predomain



datatype 'a optional = Something 'a | Nothing
text\<open>The parametric type definition of @{type optional} allows to either have something of type \<open>'a\<close>
or nothing\<close>


text\<open>The domain keyword builds a domain from continuous constructors. The resulting type is 
automatically a @{class pcpo} and additional theorems are generated (visible by \<open>print_theorems\<close>).\<close>
domain 'a llist = lNil | lCons (lazy 'a) (lazy "'a llist")
print_theorems

text\<open>From any already existing type a subtype can be defined using \<open>typedef\<close>. Here, the resulting 
subtype only contains the empty list @{const lNil}.\<close>
typedef 'a bottom = "{l. l=(lNil::'a llist)}"
  by simp

text\<open>Similarly, a subtype can be created using \<open>cpodef\<close> or \<open>pcpodef\<close>. Here, a cpo subtype of 
@{type llist} not containing the empty list is defined.\<close>
cpodef 'a nbot = "{l. l\<noteq>(lNil::'a llist)}"
  apply simp_all
  by (metis llist.con_rews(1))

record ('a) natintlist  =
  getNat :: "nat"
  getInt :: "int"
  getList :: "'a nbot"



end