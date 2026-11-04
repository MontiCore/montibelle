theory training_automaton

imports bundle.SB tscomponent.TsLocale
        training

begin





datatype S = defineState

instance S::countable
  by(countable_datatype)



definition invTransition::"unit \<Rightarrow> S \<Rightarrow> bool tone \<Rightarrow> (S \<times> bool tone) set" where
"invTransition unit = undefined"

interpretation invAut: tsWeakGen
  oops


abbreviation "invSPS \<equiv> undefined"


lemma assumes "invSPF \<in> invSPS"
  shows "internSBE.getterSB oo invSPF oo inSBE.setterSB = inverter"
  oops



definition medTransition::"unit \<Rightarrow> S \<Rightarrow> bool tone \<Rightarrow> (S \<times> bool tone) set " 
  where
"medTransition = undefined"

interpretation medAut: tsWeakGen
  oops


definition medIdTransition::" unit \<Rightarrow> S \<Rightarrow> bool tone \<Rightarrow> (S \<times> bool tone) set" 
  where
"medIdTransition = undefined"

interpretation medIdAut: tsWeakGen
  oops


abbreviation "medSPS \<equiv> undefined"

abbreviation "medIdSPS \<equiv> undefined"



theorem "medIdSPS \<subseteq> medSPS"
  oops


end