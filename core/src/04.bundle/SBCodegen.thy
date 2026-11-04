theory SBCodegen

imports SB stream.StreamCodegen 
                   
begin

instantiation sb::(chan)bot_nc
begin

definition bot_nc_sb::"'a\<^sup>\<Omega>" where "bot_nc \<equiv> least_sb"

instance
  apply(standard)
  by (simp add: SBCodegen.bot_nc_sb_def least_sb_bottom_eq)
end

lemma[code]:"Rep_lsb bot_nc = (\<lambda>c. bot_nc)"
  by (metis Rep_lsb_strict app_strict botnc_eq_bot)

default_sort "chan"

instantiation sb::("{chan}") equal
begin
definition equal_sb::"'a sb \<Rightarrow> 'a sb\<Rightarrow> bool" where                   
"equal_sb a b \<equiv>  \<forall>c. Rep_lsb a c = Rep_lsb b c"
instance
  apply intro_classes
  apply(simp add: equal_sb_def)
  using sb_rep_eqI by blast
end 

instantiation sbElem::("{equal,chan}") equal
begin
definition equal_sbElem::"'a sbElem \<Rightarrow> 'a sbElem\<Rightarrow> bool" where                   
"equal_sbElem a b \<equiv>  a = b"
instance
  apply(intro_classes)
  by(simp add: equal_sbElem_def)
end 

lemma [code abstype]: "Abs_sb (Rep_sb sb) = sb"
  by(simp add: Rep_sb_inverse)

lemma [code abstype]: "Abs_lsb (Rep_lsb sb) = sb"
  by(simp add: Rep_lsb_inverse)

lemma [code abstype]: "Abs_sbElem (Rep_sbElem sbe) = sbe"
  by(simp add: Rep_sbElem_inverse)

lemma [code]:"sbHdElemWell sb = (\<forall>c. Rep_lsb sb c \<noteq> \<epsilon>)"
  by(subst sbHdElemWell_def, simp add: sbgetch_insert2)

definition sbelem_none::"'a sbElem" where
"sbelem_none \<equiv> ( if chDomEmpty TYPE('a) then Abs_sbElem None else undefined)"

definition shd_elem ::"'cs\<^sup>\<Omega>  \<Rightarrow>'cs sbElem" where
"shd_elem sb \<equiv> ( if sbIsLeast sb then undefined else Abs_sbElem (Some (\<lambda>c. shd((sb) \<^enum> c))))"

lemma [code abstract]:"Rep_sbElem(shd_elem sb) = (if sbIsLeast sb then Rep_sbElem undefined else  (Some (\<lambda>c. shd(Rep_lsb sb c))))"
  apply(simp add: shd_elem_def) 
  apply (rule impI)
  by(subst Abs_sbElem_inverse,simp_all add: sbgetch_insert2[symmetric])

lemma [code abstract]:"Rep_sbElem(sbelem_none::'cs\<^sup>\<surd>) = (if chDomEmpty TYPE('cs) then None else Rep_sbElem undefined)"
  apply(simp add: sbelem_none_def)
  apply (rule impI)
  using sbe_emptyiff by blast

lemma [code]:"sbHdElem_h (sb::'cs\<^sup>\<Omega>) = 
       (if chDomEmpty TYPE('cs) 
          then Iup(sbelem_none) 
          else if sbIsLeast sb 
                  then Ibottom
                  else Iup(shd_elem sb))"
  apply(simp add: sbHdElem_h_def shd_elem_def sbelem_none_def)
  using inst_up_pcpo by auto

lemma [code]:"Rep_lsb(sbe2sb sbe) = (case (Rep_sbElem sbe) of Some f \<Rightarrow> \<lambda>c. \<up>(f c)
                                | None  \<Rightarrow> \<lambda>c.  \<epsilon>)"
  apply(simp add: sbe2sb_def)
  by (metis lambda_strict sbe2sb.abs_eq sbe2sb.rep_eq)

definition sbGetCh_nc ::"'cs1 \<Rightarrow> 'cs2\<^sup>\<Omega> \<Rightarrow> M stream" where
"sbGetCh_nc = (\<lambda>c. Rep_cfun(sbGetCh c))"
                                          
lemma [code_abbrev]:"sbGetCh_nc c sb = sbGetCh c\<cdot>sb"
  by(simp add: sbGetCh_nc_def sbGetCh_def)

lemma [code]:"sbGetCh_nc c (sb::'cs2\<^sup>\<Omega>) = ((if Rep c\<in>chDom TYPE('cs2) then Rep_lsb sb (Abs(Rep c)) else \<epsilon>))"
  by(simp add: sbGetCh_nc_def sbGetCh_def cont2cont_fun)

lemma [ccodeAbs]:"Rep_lsb(sbTypeCast\<cdot>sb) = (\<lambda>c. sbGetCh c\<cdot>sb) "
  by(simp add: sbTypeCast.rep_eq)
 
lemma [ccodeAbs]:"Rep_lsb (sbUnion\<cdot>(sb1::'cs1\<^sup>\<Omega>)\<cdot>sb2) =  (\<lambda> c. 
                  if Rep c \<in> chDom TYPE('cs1) 
                  then sb1 \<^enum>\<^sub>\<star> c 
                  else sb2 \<^enum>\<^sub>\<star> c)"
  by(simp add: sbunion_rep_eq)

lemma [ccodeAbs]:"Rep_lsb (sbTake a\<cdot>b) =  (\<lambda>c. stake a\<cdot>(Rep_lsb b c))"
  by(simp add: sbTake.rep_eq sbgetch_insert2[symmetric])

lemma [ccodeAbs]:"Rep_lsb (sbDrop a\<cdot>b) = (\<lambda>c. sdrop a\<cdot>(Rep_lsb b c))"
  by(simp add: sbDrop.rep_eq sbgetch_insert2[symmetric])

lemma sbconc_c[ccodeAbs]:"Rep_lsb (sbConc sb1\<cdot>sb2) =  (\<lambda>c. sconc_nc (Rep_lsb sb1 c) (Rep_lsb sb2 c))"
  by(simp add: sbConc.rep_eq sconc_nc_def sbgetch_insert2[symmetric])

lemma [code]:"Rep_cfun (conc sb) = sbConc_nc sb"
  by(simp add: conc_sb_def sbConc_nc_def)

thm sbConc_nc_def
thm sbConc_code_abbrev
thm c2_nc

definition botsb::"'a::chan sb" where
"botsb \<equiv> Abs_lsb (\<lambda>c.  \<epsilon>)"

lemma [code]:"Rep_lsb botsb = (\<lambda>c. \<epsilon>)"
  by(simp add: botsb_def)

lemma botsb_eq:"botsb = \<bottom>"
  by(simp add: bot_sb botsb_def)

definition fix_nc::"('a sb \<rightarrow> 'a sb) \<Rightarrow> nat \<Rightarrow> 'a sb" where
"fix_nc F x = (\<Squnion>i. iterate i\<cdot>F\<cdot>botsb)"

lemma[code]:"fix_nc f x = (if iterate_nc x f botsb = iterate_nc(x+1) f botsb
                     then iterate_nc x f botsb else fix_nc f (x+1))"
  apply(simp add: fix_nc_def iterate_nc_def botsb_eq)
  apply auto[1]
  by (metis (no_types, lifting) iterate_fix_eq lub_eq)

code_datatype "(Abs_union)"

code_datatype "(Abs_minus)"

lemma[code]:"(Rep_union:: 'a \<union> 'b \<Rightarrow> channel) ( Abs_union a) = (if a \<in> chDom TYPE('a) \<or>
a \<in> chDom TYPE('b)  then a else (Rep_union:: 'a \<union> 'b \<Rightarrow> channel) ( Abs_union a)) "
  apply auto[1]
  by (metis (full_types) Abs_union_inverse Diff_empty Diff_iff Un_iff)+

lemma[code]:"(Rep_minus:: 'a - 'b \<Rightarrow> channel) ( Abs_minus a) = (if a \<in> chDom TYPE('a) \<and>
 a \<notin> chDom TYPE('b) then a else (Rep_minus:: 'a - 'b \<Rightarrow> channel) (Abs_minus a)) "
  apply auto[1]
  by (meson Abs_minus_inverse Diff_iff subsetD)

lemma [code]: "Rep_sb sb = sblegacy2new (Rep_lsb sb)"
  apply(simp add: Rep_lsb_def)
  by (metis
      Abs_lsb_def
      Abs_sb_inverse
      Rep_lsb_def
      abs_rep_sb_sb
      legacy2new_well
      mem_Collect_eq
      rep_sb_well
  )

definition mstream2combined_nc :: "timeType \<Rightarrow> M stream \<Rightarrow> msg combinedstream"
  where "mstream2combined_nc \<equiv> (\<lambda>tt. Rep_cfun (mstream2combined tt))"

lemma [code_abbrev]:
  "mstream2combined_nc tt s = mstream2combined tt\<cdot>s"
  by(simp add: mstream2combined_nc_def)

definition inv_Untimed :: "M \<Rightarrow> msg" where
  "inv_Untimed \<equiv> inv Untimed"

lemma [code]: "(inv_Untimed) (Untimed x) = x"
  by (simp add: inv_Untimed_def)

lemma [code_abbrev]: "inv_Untimed = inv Untimed"
  by (simp add: inv_Untimed_def)

definition inv_TLive :: "M \<Rightarrow> msg event" where
  "inv_TLive \<equiv> inv (Timed o TLive)"

lemma [code]: "(inv_TLive) ((Timed (TLive x))) = x"
  apply (simp add: inv_TLive_def o_def)
  by (simp add: inj_def inv_into_f_eq)

lemma [code_abbrev]: "inv_TLive = inv (Timed o TLive)"
  by (simp add: inv_TLive_def)

definition inv_TFin :: "M \<Rightarrow> msg list" where
  "inv_TFin \<equiv> inv (Timed o TFin)"

lemma [code]: "(inv_TFin) ((Timed (TFin x))) = x"
  apply (simp add: inv_TFin_def o_def)
  by (simp add: inj_def inv_into_f_eq)

lemma [code_abbrev]: "inv_TFin = inv (Timed o TFin)"
  by (simp add: inv_TFin_def)

definition inv_TOne :: "M \<Rightarrow> msg tone" where
  "inv_TOne \<equiv> inv (Timed o TOne)"

lemma [code]: "(inv_TOne) ((Timed (TOne x))) = x"
  apply (simp add: inv_TOne_def o_def)
  by (simp add: inj_def inv_into_f_eq)

lemma [code_abbrev]: "inv_TOne = inv (Timed o TOne)"
  by (simp add: inv_TOne_def)


definition inv_Tsyn :: "M \<Rightarrow> msg tsyn" where
  "inv_Tsyn \<equiv> inv (Timed o Tsyn)"

lemma [code]: "(inv_Tsyn) ((Timed (Tsyn x))) = x"
  apply (simp add: inv_Tsyn_def o_def)
  by (simp add: inj_def inv_into_f_eq)

lemma [code_abbrev]: "inv_Tsyn =  inv (Timed o Tsyn)"
  by (simp add: inv_Tsyn_def)

lemma [code]: "mstream2combined_nc TTLive s = TEVENT (smap (inv (Timed o TLive))\<cdot>s)"
  apply(simp add: mstream2combined_nc_def)
  apply(rule beta_cfun_cont_fun)
  by simp

lemma [code]: "mstream2combined_nc TUntimed s = UNTIMED (smap (inv Untimed)\<cdot>s)"
  apply(simp add: mstream2combined_nc_def)
  apply(rule beta_cfun_cont_fun)
  by simp

lemma [code]: "mstream2combined_nc TTFin s = TSLICED (smap (inv (Timed o TFin))\<cdot>s)"
  apply(simp add: mstream2combined_nc_def)
  apply(rule beta_cfun_cont_fun)
  by simp

lemma [code]: "mstream2combined_nc TTOne s = TONE (smap (inv (Timed o TOne))\<cdot>s)"
  apply(simp add: mstream2combined_nc_def)
  apply(rule beta_cfun_cont_fun)
  by simp

lemma [code]: "mstream2combined_nc TTsyn s = TSYN (smap (inv (Timed o Tsyn))\<cdot>s)"
  apply(simp add: mstream2combined_nc_def)
  apply(rule beta_cfun_cont_fun)
  by simp

end
