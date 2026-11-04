theory TSPSFun

imports SPSFun spf.TSPFfunction
         
begin

definition spsComp_strong::
"('I1::tchan\<^sup>\<Omega> \<rightarrow>\<^sub>s 'O1::tchan\<^sup>\<Omega>) set \<Rightarrow> ('I2::tchan\<^sup>\<Omega> \<rightarrow>\<^sub>s 'O2::tchan\<^sup>\<Omega>) set \<Rightarrow> 
  ((('I1 \<union> 'I2) - 'O1 \<union> 'O2)\<^sup>\<Omega> \<rightarrow>\<^sub>s ('O1 \<union> 'O2)\<^sup>\<Omega>) set" (infixr "\<Otimes>\<^sub>s" 70) 
where "spsComp_strong F G = {f \<otimes>\<^sub>s g | f g. f\<in>F \<and> g\<in>G }"

definition spsMakeWeak :: "('a::{one_chan,tchan} untimed\<^sup>\<Omega> \<rightarrow> 'b::{one_chan,tchan} untimed\<^sup>\<Omega>) \<Rightarrow> ('a\<^sup>\<Omega> \<rightarrow>\<^sub>w 'b\<^sup>\<Omega>) set" where
"spsMakeWeak spf = {spf'. 
        spf oo convUntimed = convUntimed oo (Rep_tspfw_fun\<cdot>spf')}"

definition spsMakeStrong :: "('a::{one_chan,tchan} untimed\<^sup>\<Omega> \<rightarrow> 'b::{one_chan,tchan} untimed\<^sup>\<Omega>) \<Rightarrow> ('a\<^sup>\<Omega> \<rightarrow>\<^sub>s 'b\<^sup>\<Omega>) set" where
"spsMakeStrong spf = {spf'. 
        spf oo convUntimed = convUntimed oo (Rep_tspfs_fun\<cdot>spf')}"

end