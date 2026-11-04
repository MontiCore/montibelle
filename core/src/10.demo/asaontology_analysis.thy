theory asaontology_analysis
  imports asaontology 
begin

lemma reachability_transitive_example:
  "reachable1 ASAOntology ComponentProduct UserStory"
  apply(subst ASAOnt.not_reachable,simp_if_one rules: ASAOntologyEdges_def ASAOntologyVertices_def arcs_ends_def arc_to_ends_def)?
  apply(simp add: ASAOnt.Ontology_def reachable_def)?
  apply(simp add: ASAOntologyEdges_def ASAOntologyVertices_def arcs_ends_def arc_to_ends_def)? 
  oops (* autosledgi*)


lemma reachability_transitive_example:
  "reachable1 ASAOntology Component ComponentProduct"
  apply(subst ASAOnt.not_reachable,simp_if_one rules: ASAOntologyEdges_def ASAOntologyVertices_def arcs_ends_def arc_to_ends_def)?
  apply(simp add: ASAOnt.Ontology_def reachable_def)?
  apply(simp add: ASAOntologyEdges_def ASAOntologyVertices_def arcs_ends_def arc_to_ends_def)? 
  oops (* autosledgi *)

lemma quelle_example:
  "quelle ASAOntology ComponentProduct"
  apply(simp add: ASAOnt.Ontology_def quelle_def)?
  apply(simp add: ASAOntologyEdges_def ASAOntologyVertices_def)?
  oops (* autosledgi *)

lemma senke_example:
  "senke ASAOntology Component"
  apply(simp add: ASAOnt.Ontology_def senke_def)?
  apply(simp add: ASAOntologyEdges_def ASAOntologyVertices_def)?
  oops (* autosledgi *)


end