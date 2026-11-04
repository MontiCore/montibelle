theory TSPFfunction

imports SPF bundle.TSBFunction
         
begin

definition spfInputRestrict :: "'I::chan set \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O::chan\<^sup>\<Omega>) \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"spfInputRestrict C \<equiv> (\<Lambda> spf. spf oo (\<Lambda> sb. (Abs_lsb (\<lambda>c. if c \<in> C then sb \<^enum> c else \<epsilon>))))"

definition spfInputRestrictAlt :: "'UA myself \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O::chan\<^sup>\<Omega>) \<rightarrow> (('I - 'UA)\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"spfInputRestrictAlt _ \<equiv> \<Lambda> spf. spf oo sbTypeCast"

definition spfOutputRestrict :: "'O::chan set \<Rightarrow> ('I::chan\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"spfOutputRestrict C \<equiv> (\<Lambda> spf. (\<Lambda> sb. (Abs_lsb (\<lambda>c. if c \<in> C then sb \<^enum> c else \<epsilon>))) oo spf)"

definition spfOutputRestrictAlt :: "'UA myself \<Rightarrow> ('I::chan\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow> ('O - 'UA)\<^sup>\<Omega>)" where
"spfOutputRestrictAlt _ \<equiv> \<Lambda> spf. sbTypeCast oo spf"

definition tspfInputDrop :: "nat \<Rightarrow> ('I::tchan\<^sup>\<Omega> \<rightarrow> 'O::tchan\<^sup>\<Omega>) \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"tspfInputDrop n \<equiv> (\<Lambda> spf. spf oo (tsbDrop n))"

definition tspfOutputDrop :: "nat \<Rightarrow> ('I::tchan\<^sup>\<Omega> \<rightarrow> 'O::tchan\<^sup>\<Omega>) \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"tspfOutputDrop n \<equiv> (\<Lambda> spf. (tsbDrop n) oo spf)"

definition tspfInputTake :: "nat \<Rightarrow> ('I::tchan\<^sup>\<Omega> \<rightarrow> 'O::tchan\<^sup>\<Omega>) \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"tspfInputTake n \<equiv> (\<Lambda> spf. spf oo (tsbTake n))"

definition tspfOutputTake :: "nat \<Rightarrow> ('I::tchan\<^sup>\<Omega> \<rightarrow> 'O::tchan\<^sup>\<Omega>) \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"tspfOutputTake n \<equiv> (\<Lambda> spf. (tsbTake n) oo spf)"

definition spfOutputConc :: "'O::chan\<^sup>\<Omega> \<Rightarrow> ('I::chan\<^sup>\<Omega> \<rightarrow> 'O::chan\<^sup>\<Omega>) \<Rightarrow> 'I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>" where
"spfOutputConc sb spf \<equiv> (\<Lambda> i. sbConc sb\<cdot>(spf\<cdot>i))"
                                                                   
definition spfInputConc :: "'I::chan\<^sup>\<Omega> \<Rightarrow> ('I::chan\<^sup>\<Omega> \<rightarrow> 'O::chan\<^sup>\<Omega>) \<Rightarrow> 'I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>" where
"spfInputConc sb spf \<equiv> (\<Lambda> i. spf\<cdot>(sbConc sb\<cdot>i))"

definition tspfDelayInput :: "nat \<Rightarrow> ('I::{tchan,countable}\<^sup>\<Omega> \<rightarrow> 'O::{tchan,countable}\<^sup>\<Omega>) \<Rightarrow> 'I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>" where
"tspfDelayInput n spf \<equiv> spfInputConc (n \<diamondop> sbInfTlen) spf"

definition tspfDelayOutput :: "nat \<Rightarrow> ('I::{tchan,countable}\<^sup>\<Omega> \<rightarrow> 'O::{tchan,countable}\<^sup>\<Omega>) \<Rightarrow> 'I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>" where
"tspfDelayOutput n spf \<equiv> spfOutputConc (n \<diamondop> sbInfTlen) spf"

definition tspfDelayAtMost :: "nat \<Rightarrow> ('I::{countable, tchan, one_chan}\<^sup>\<Omega> \<rightarrow> 'O::{countable, tchan, one_chan}\<^sup>\<Omega>) \<Rightarrow> ('I::{countable, tchan, one_chan}\<^sup>\<Omega> \<rightarrow> 'O::{countable, tchan, one_chan}\<^sup>\<Omega>) set" where
"tspfDelayAtMost n spf = {f. \<forall> i c. #\<^sub>\<surd> (spf\<cdot>i \<^enum> c) + n \<ge> #\<^sub>\<surd> (f\<cdot>i \<^enum> c) \<and>
                                 convUntimed\<cdot>(spf\<cdot>i) = convUntimed\<cdot>(f\<cdot>i)}"

definition tspfDelayAtLeast :: "nat \<Rightarrow> ('I::{countable, tchan, one_chan}\<^sup>\<Omega> \<rightarrow> 'O::{countable, tchan, one_chan}\<^sup>\<Omega>) \<Rightarrow> ('I::{countable, tchan, one_chan}\<^sup>\<Omega> \<rightarrow> 'O::{countable, tchan, one_chan}\<^sup>\<Omega>) set" where
"tspfDelayAtLeast n spf = {f. \<forall> i c. #\<^sub>\<surd> (spf\<cdot>i \<^enum> c) + n \<le> #\<^sub>\<surd> (f\<cdot>i \<^enum> c) \<and>
                                 convUntimed\<cdot>(spf\<cdot>i) = convUntimed\<cdot>(f\<cdot>i)}"

definition tspfDelayMinMax :: "nat \<times> nat \<Rightarrow> ('I::{countable, tchan, one_chan}\<^sup>\<Omega> \<rightarrow> 'O::{countable, tchan, one_chan}\<^sup>\<Omega>) \<Rightarrow> ('I::{countable, tchan, one_chan}\<^sup>\<Omega> \<rightarrow> 'O::{countable, tchan, one_chan}\<^sup>\<Omega>) set" where
"tspfDelayMinMax bound spf = tspfDelayAtLeast (fst bound) spf \<inter> tspfDelayAtMost (snd bound) spf "


definition tspfEventConverter :: "('a tlived\<^sup>\<Omega> \<rightarrow> 'b:: {echan}\<^sup>\<Omega>)
                                \<rightarrow> 'a:: {tchan, one_chan}\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>" where
"tspfEventConverter \<equiv> \<Lambda> spf. spf oo convEvent"

definition tspfUntimedConverter :: "('a untimed\<^sup>\<Omega> \<rightarrow> 'b:: {echan}\<^sup>\<Omega>)
                                \<rightarrow> 'a:: {tchan, one_chan}\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>" where
"tspfUntimedConverter \<equiv> \<Lambda> spf. spf oo convUntimed"
end