
signature HOLCFcodegen =
sig
  val mk_non_cont : theory -> string -> theory -> theory
  val mk_code_abbrev : string -> Context.generic -> Context.generic 
end;

val dot = "."
val rep_cfun = "Cfun.cfun.Rep_cfun"
val cfun = "Cfun.cfun"
val str_fun = "fun"
val str_a = "a"
val str_c = "c"
val nc = "_nc"
val def = "_def"
val str_code_abbrev = "_code_abbrev"

fun get_code_abbrev thy = Attrib.attribute (Proof_Context.init_global thy) (hd @{attributes [code_abbrev]})

fun get_thm_parents_h (x::xs) thm_name = 
    if Global_Theory.defined_fact x ((Context.theory_base_name x)^dot^thm_name) then 
      ((Global_Theory.get_thm x thm_name),x) 
    else 
      get_thm_parents_h ((Theory.parents_of x)@xs) thm_name
  |get_thm_parents_h [] _ = error ("Thm not found")

fun get_thm_parents thy thm_name = 
  if Global_Theory.defined_fact thy ((Context.theory_base_name thy)^dot^thm_name) then 
    ((Global_Theory.get_thm thy thm_name),thy) 
  else 
    get_thm_parents_h (Theory.parents_of thy) thm_name

fun get_name_sig (t1 $ t2 $ _) = if #1(Term.dest_Const(t1)) = rep_cfun then 
      get_name_sig t2 
    else 
      Term.dest_Const(t1)
  |get_name_sig (t1 $ t2) = if #1(Term.dest_Const(t1)) = rep_cfun then 
      get_name_sig t2 
    else 
      Term.dest_Const(t1)
  |get_name_sig t1 = if Term.is_Const t1 then 
      Term.dest_Const(t1) 
    else 
      ("",dummyT)

fun make_sign [] = dummyT 
  |make_sign [x] = x
  |make_sign (x::xs) = x-->make_sign xs

fun termdest_all a = if Term.is_TVar a then 
    [(a,2)] 
  else 
    (if (#1 (Term.dest_Type a) = str_fun) then 
      (hd (#2 (Term.dest_Type a)),0) ::termdest_all(hd( tl (#2 (Term.dest_Type a)))) 
    else 
      (if (#1 (Term.dest_Type a) = cfun) then 
        (hd (#2 (Term.dest_Type a)),1) ::termdest_all(hd( tl (#2 (Term.dest_Type a)))) 
      else 
        [(a,2)]))

fun make_rhs_h 0 _ _ _=  error("make rhs")
  |make_rhs_h 1 _ f _= Const (f , dummyT)
  |make_rhs_h x y f l= if (hd l = 1) then 
      Const (rep_cfun, dummyT) $ make_rhs_h (x-1) y f (tl l) $ Bound (y-x) 
    else 
      make_rhs_h (x-1) y f (tl l) $ Bound (y-x)

fun make_rhs 1 y f l = make_rhs_h y y f l
  |make_rhs x y f l = Abs((str_a^(Int.toString(y-x))),(dummyT), make_rhs (x-1) y f l)


fun mk_def name p q =
  let val nameb = Binding.make(name,p)
    val ty_global = dummyT
    val args = (((SOME(nameb,SOME ty_global,NoSyn),(Binding.empty_atts,q)),[]),[])
    val cmd = (fn (((decl, spec), prems), params) =>
      #2 o (Specification.definition decl params prems spec))
  in 
    cmd args
  end;

fun dest_const_var x = if Term.is_Const x then 
    Term.dest_Const x 
  else 
    dest_const_var(#1(Term.dest_comb x))

fun tle [] = []
|tle (_::xs) = xs

fun mk_lemma_rhs name sign [] _ _ _ = Const (name, sign)
  |mk_lemma_rhs name sign _ _ _ 0 = Const (name, sign)
  |mk_lemma_rhs name sign w x z y = if (hd w = 1) then 
      Const (rep_cfun, hd z) $ mk_lemma_rhs name sign (tle w) (tle x) (tle z) (y-1) $ Var ((str_a^(Int.toString (y-1)), 0), hd x) 
    else
       mk_lemma_rhs name sign (tle w) (tle x) (tle z) (y-1) $ Var ((str_a^(Int.toString (y-1)), 0),hd  x)

fun mk_var [] _ = [] 
  |mk_var [x] y = [Var ((str_a^(Int.toString (y-1)), 0), x)] 
  |mk_var (x::xs) y = Var ((str_a^(Int.toString (y-1)), 0), x) :: mk_var (xs) (y+1)

fun get_cfuntype_list (t1 $ t2 $ _) = #2(Term.dest_Const(t1))::get_cfuntype_list (t2)
  |get_cfuntype_list _ = []

fun split_t_name (x::xs) ys = if (str x = dot) then 
    (String.implode ys, String.implode xs) 
  else 
    split_t_name xs (ys@[x])
  | split_t_name [] _ = error("name has no .")

fun get_clemma_name x thy = if  (Global_Theory.defined_fact thy (Context.theory_base_name thy^dot^str_c^(Int.toString(x))^nc)) then 
    get_clemma_name (x+1) thy
  else 
    str_c^Int.toString(x)^nc

fun get_fun_name t = if #1(Term.dest_Const(#1(strip_comb t))) = rep_cfun then 
    get_fun_name (hd(#2(strip_comb t)))
  else 
    (if Term.is_Const t then 
      (#1 (dest_Const t))
    else
      (#1(Term.dest_Const(#1(strip_comb t)))))

fun make_code_lhs t x name = if #1(Term.dest_Const(#1(strip_comb t))) = rep_cfun then 
    make_code_lhs (hd(#2(strip_comb t))) (x@(tl(#2(strip_comb t)))) name 
  else 
    (if Term.is_Const t then 
      list_comb(Const(name, make_sign(map #1 (termdest_all (#2(dest_Const t))))),rev x) 
    else
      list_comb(Const(name ,make_sign(map #1 (termdest_all(#2(Term.dest_Const(#1(strip_comb t))))))), #2(strip_comb t)@x))

fun mk_non_cont_h (def:thm) (name:string) (f:(string * typ -> string) option) = 
  let 
    val full_prop_def:term = Thm.full_prop_of def
    val name_sig:(string*typ) = (case full_prop_def of
      Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => get_name_sig(#2(Term.dest_comb(#1(Term.dest_comb(#2(Term.dest_comb full_prop_def))))))
      | _ => get_name_sig(#2(Term.dest_comb(#1(Term.dest_comb full_prop_def)))));
    val real_name:string = if not (Option.isSome f) then 
        name 
      else 
        ((Option.valOf f) name_sig)
    val type_list:(typ * int) list = termdest_all (#2 name_sig)
    val fun_type_list:(int list) =  tl (rev (List.map #2 type_list))
    val rhs:term = make_rhs (length type_list) (length type_list) (#1 name_sig) fun_type_list
    val term_nc:term = HOLogic.mk_eq (Free((real_name^nc),dummyT) ,rhs);
  in 
    (HOLogic.mk_Trueprop term_nc,real_name)
  end

fun mk_non_cont (thy:theory) (name:string) = 
  let
    val theory_base_name:string = Context.theory_base_name (#2(get_thm_parents thy (name^def)))
    val theory_base_name_size:int = size theory_base_name
    val def:thm = #1(get_thm_parents thy (name^def))
    val lemma_name:(term * string) = mk_non_cont_h def name (SOME(fn x => substring(#1 x, (theory_base_name_size+1) ,((size (#1 x)) -(theory_base_name_size+1))))) 
  in 
    Named_Target.theory_map (mk_def ((#2 lemma_name)^nc) @{here} (#1 lemma_name))
  end;

fun mk_non_cont_domain (thy:theory) (name:string) = 
  let
    val def:thm = Global_Theory.get_thm thy (name^def)
    val lemma_name:(term * string) = mk_non_cont_h def name NONE
  in
    Named_Target.theory_map (mk_def ((#2 lemma_name)^nc) @{here} (#1 lemma_name))
  end;

fun mk_code_abbrev_proof def pc prop = let
    val pc = Simplifier.add_simp def pc
  in
    Goal.prove pc [][] prop (fn _ => simp_tac pc 1)
  end;

fun mk_code_abbrev (name:string) (context:Context.generic) = 
  let
    val def:thm = Context.cases Global_Theory.get_thm (Proof_Context.get_thm) context (name^nc^def)
    val nc_name:string =  #1(Term.dest_Const(#1(HOLogic.dest_eq(HOLogic.dest_Trueprop(Thm.full_prop_of def)))))
    val nc_def_split:term = strip_abs_body(#2(Term.dest_comb(#2(Term.dest_comb(Thm.full_prop_of def)))))
    val name_sig:(string*typ) = get_name_sig(nc_def_split)
    val cfuntype_list:(typ list) = get_cfuntype_list(nc_def_split)
    val type_list:(typ list) = map #1 (termdest_all (#2 name_sig))
    val fun_type_list:(int list) = map #2 (termdest_all (#2 name_sig))
    val sign:typ = make_sign type_list;
    val var_list:(term list) = mk_var (List.take(type_list, List.length(type_list)-1)) 1;
    val lemma_lhs:term = list_comb (Const (nc_name, sign), var_list);
    val lemma_rhs:term = mk_lemma_rhs (#1 name_sig) (#2 name_sig) (tl(rev fun_type_list))  (List.rev (List.take(type_list, List.length(type_list)-1))) cfuntype_list (List.length(type_list)-1);
    val lemma_nc:term = HOLogic.mk_eq (lemma_lhs ,lemma_rhs);
    val lemma_prop_nc:term = HOLogic.mk_Trueprop lemma_nc
    val pc:Proof.context = Context.cases Proof_Context.init_global I context
    val lemma:thm = mk_code_abbrev_proof def pc lemma_prop_nc
  in Context.mapping(Named_Target.theory_map(
    Local_Theory.note (((Binding.make (name^str_code_abbrev,@{here})),      
    [Attrib.internal @{here} (K (Context.cases(get_code_abbrev) (get_code_abbrev o Proof_Context.theory_of) context))]), ([lemma])) #> snd )) I context 
  end;

fun mk_code_abbrev_b thy typ = 
  let 
    val nc_def:thm = (Global_Theory.get_thm thy (typ^"_bottom_nc_def"))
    val lemma:thm = mk_code_abbrev_proof nc_def (Proof_Context.init_global thy) (Thm.full_prop_of nc_def)
  in
    Named_Target.theory_map(
    Local_Theory.note (((Binding.make ((typ^"_bottom_code_abbrev"),@{here})),
    [Attrib.internal @{here} (K (get_code_abbrev thy))]), ([lemma])) #> snd )
  end      
 
fun cnc_intern lhs thm context = 
  let
    val fun_name = get_fun_name lhs
    val fun_name_split =split_t_name(String.explode fun_name) [] 
    val theory_base_name = Thm.theory_base_name thm
    val thy = Context.cases(I)(Proof_Context.theory_of) context
    val fun_name = #2 fun_name_split
    val context = if Global_Theory.defined_fact thy (theory_base_name^dot^fun_name^nc^def) then 
        context
      else 
        (Context.mapping (mk_non_cont thy fun_name)(Proof_Context.background_theory(mk_non_cont thy fun_name))) context
    val context = if Global_Theory.defined_fact thy (theory_base_name^dot^fun_name^str_code_abbrev) then 
        context
      else 
        mk_code_abbrev fun_name context
  in
    context
  end


fun codelemma_nc int thm context =
  let
    val thy:theory = Context.cases(I)(Proof_Context.theory_of) context
    val d:term = Thm.full_prop_of thm
    val lhs_comb = Term.dest_comb (#2 (Term.dest_comb(#1(Term.dest_comb(#2(Term.dest_comb(d)))))))
    val lhs = if int = 0 then #1 lhs_comb $ #2 lhs_comb else #2 lhs_comb
    val fun_name:string = get_fun_name lhs
    val fun_name_split:(string*string) = split_t_name(String.explode fun_name) []
    val nc_name:string = (Context.theory_base_name thy)^dot^(#2 fun_name_split)^nc
    val clhs:term = if int = 0 then (make_code_lhs lhs [] nc_name) else (#1 lhs_comb) $ (make_code_lhs lhs [] nc_name)
    val rhs:term = #2(Term.dest_comb(#2(Term.dest_comb(d))))
    val clemma_nc:term = HOLogic.mk_eq (clhs ,rhs);
    val clemma_prop_nc:term = HOLogic.mk_Trueprop clemma_nc
    val theory_base_name:string = Context.theory_base_name thy
    val theory_base_name_size:int = size theory_base_name
    val fun_name:string = substring(nc_name, (theory_base_name_size+1) ,((size (nc_name)) -(theory_base_name_size+4)))
    val pc:Proof.context = Proof_Context.init_global thy
    val nc_def:thm = Global_Theory.get_thm thy (fun_name^"_nc_def")
    val thm = Simplifier.simplify pc thm
    val pc:Proof.context = Simplifier.add_simp thm pc 
    val pc:Proof.context = Simplifier.add_simp nc_def pc
    val lemma = Goal.prove pc [][] clemma_prop_nc (fn _ => safe_simp_tac pc 1)
    val code:attribute = Attrib.attribute (Proof_Context.init_global thy) (hd @{attributes [code]})
    val name:string = get_clemma_name 0 thy
  in
    Context.mapping(Named_Target.theory_map(Local_Theory.note (((Binding.make ((name),@{here})),
      [Attrib.internal @{here} (K code)]), ([lemma])) #> snd))(I) context 
  end

fun cnc thm context = 
  let
    val d = Thm.full_prop_of thm
    val lhs = (#2 (Term.dest_comb(#1(Term.dest_comb(#2(Term.dest_comb(d)))))))
    val context = cnc_intern lhs thm context
    val context = codelemma_nc 0 thm context
  in 
    context
  end;
 
fun sbcnc thm context = 
  let
    val d = Thm.full_prop_of thm
    val lhs_comb = Term.dest_comb (#2 (Term.dest_comb(#1(Term.dest_comb(#2(Term.dest_comb(d)))))))
    val lhs =  #2 lhs_comb 
    val context = cnc_intern lhs thm context 
    val context = codelemma_nc 1 thm context
  in                    
    context
  end  

fun mk_non_cont_domain_all _ thy [n] = mk_non_cont_domain thy n |
    mk_non_cont_domain_all typ thy (n::ns) = (mk_non_cont_domain thy n) o mk_non_cont_domain_all typ thy (ns) |
    mk_non_cont_domain_all _ _ [] = error("Error in HOLCFGen Code")

fun mk_code_abbrev_all _ [n] = Context.theory_map(mk_code_abbrev n) |
    mk_code_abbrev_all thy (n::ns) = (Context.theory_map(mk_code_abbrev n)) o mk_code_abbrev_all thy (ns) |
    mk_code_abbrev_all _ [] = error("Error in HOLCFGen Code")

fun add_nc_list [] = []
|add_nc_list (x::xs) = x^nc :: add_nc_list xs

fun make_cons_list _ [] = []
| make_cons_list thy (x::xs) = #1(HOLogic.dest_eq(HOLogic.dest_Trueprop(Thm.full_prop_of
(Global_Theory.get_thm (thy) (x^def))))) :: make_cons_list thy (xs)
                                

fun quickcheck_gen thy con_nc name tyco  = let
  val ctxt = Proof_Context.init_global thy
val constrs = map (Syntax.read_term ctxt) (con_nc)
val vs = map dest_TFree (snd (dest_Type (body_type (fastype_of (hd constrs)))))
fun mk_dconstrs (Const (s, T)) =
          (s, map (Old_Datatype_Aux.dtyp_of_typ [(tyco, vs)]) (binder_types T))
      | mk_dconstrs t =
          error (Syntax.string_of_term ctxt t ^
            " is not a valid constructor for quickcheck_generator, which expects a constant.")
fun the_descr _ _ =
      let val descr = [(0, (tyco, map Old_Datatype_Aux.DtTFree vs, map mk_dconstrs constrs))]
      in (descr, vs, [tyco], name, ([name], []), ([Type (tyco, map TFree vs)], [])) end
fun ensure_sort (sort, instantiate) =
      Quickcheck_Common.ensure_sort
        (((\<^sort>\<open>typerep\<close>, \<^sort>\<open>term_of\<close>), sort), (the_descr, instantiate))
        Old_Datatype_Aux.default_config [tyco]
in
    thy
    |> ensure_sort
        (\<^sort>\<open>full_exhaustive\<close>, Exhaustive_Generators.instantiate_full_exhaustive_datatype)
    |> ensure_sort (\<^sort>\<open>exhaustive\<close>, Exhaustive_Generators.instantiate_exhaustive_datatype)
    |> ensure_sort (\<^sort>\<open>random\<close>, Random_Generators.instantiate_random_datatype)
    |> I
end 

fun setupdomain list thy = let
val context = Context.the_local_context(Context.>>(I))
val typ = Proof_Context.read_typ_abbrev context (hd list)
val constructors = tl list
val tyco = (#1 o dest_Type) typ
val name = Long_Name.base_name tyco
val term_nc = HOLogic.mk_eq (Free((name^"_bottom_nc"),typ) ,Const("Cpo.pcpo_class.bottom", typ));
val term_prop_nc = HOLogic.mk_Trueprop term_nc
val thy = Named_Target.theory_map (mk_def ((name^"_bottom_nc")) @{here} term_prop_nc) thy
val thy = (mk_code_abbrev_b thy name) thy
val thy = (mk_non_cont_domain_all typ thy constructors) thy 
val thy = (mk_code_abbrev_all thy constructors) thy
val con_nc = (name^"_bottom_nc")::(add_nc_list constructors)
val thy = Code.declare_datatype_cmd con_nc thy
val thy = quickcheck_gen thy con_nc name tyco
in 
  thy
end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>setup_domain\<close>
    "setup domain for quickcheck"
    (Scan.repeat1 Parse.string >> (Toplevel.theory o setupdomain));

