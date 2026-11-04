theory req_dreamconformasaont
  imports asaontology dreaminstance
begin

theorem conformity: "conform DreamInstance ASAOntology"
  apply(simp add: conform_def)
  apply rule
  apply eval?
  apply rule? 
  apply eval?
  apply eval?
  oops (* autosledgi *)

end