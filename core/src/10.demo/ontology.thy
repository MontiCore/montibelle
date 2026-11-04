theory asaontology
  imports ClassDiagramAnalyses
begin



abbreviation "ComponentProduct \<equiv>  (''Component (Product)'' ,''Component (Product)'')"
abbreviation "FunctionalSystem \<equiv>  (''FunctionalSystem'', ''FunctionalSystem'')"
abbreviation "UserStory \<equiv>  (''UserStory'' ,''UserStory'')"
abbreviation "RequirementOccurence \<equiv>  (''RequirementOccurence'', ''RequirementOccurence'')"
abbreviation "FunctionOccurence \<equiv>  (''FunctionOccurence'', ''FunctionOccurence'')"
abbreviation "FunctionalPartOccurence \<equiv>  (''FunctionalPartOccurence'' ,''FunctionalPartOccurence'')"
abbreviation "ComponentOccurence \<equiv>  (''ComponentOccurence'' ,''ComponentOccurence'')"
abbreviation "Requirement \<equiv>  (''Requirement'', ''Requirement'')"
abbreviation "Function \<equiv>  (''Function'', ''Function'')"
abbreviation "FunctionalPart \<equiv>  (''FunctionalPart'' ,''FunctionalPart'')"
abbreviation "Component \<equiv>  (''Component'', ''Component'')"
abbreviation "FunctionGroup \<equiv>  (''FunctionGroup'', ''FunctionGroup'')"
abbreviation "FunctionalPartGroup \<equiv>  (''FunctionalPartGroup'', ''FunctionalPartGroup'')"
abbreviation "ComponentGroup \<equiv>  (''ComponentGroup'', ''ComponentGroup'')"
definition ASAOntologyVertices::"vertex set"where
"ASAOntologyVertices = {ComponentProduct,
                        FunctionalSystem,
                        UserStory,
                        RequirementOccurence,
                        FunctionOccurence, 
                        FunctionalPartOccurence, 
                        ComponentOccurence, 
                        Requirement, 
                        Function, 
                        FunctionalPart, 
                        Component, 
                        FunctionGroup, 
                        FunctionalPartGroup, 
                        ComponentGroup}"



abbreviation "componentproduct2functionalsystem \<equiv> \<lparr>source = ComponentProduct, target = FunctionalSystem, name = ''isA'', cardinality = OneMany \<rparr>"
abbreviation "functionalsystem2userstory \<equiv> \<lparr>source = FunctionalSystem, target = UserStory, name = ''covers'', cardinality = OneMany \<rparr>"
abbreviation "userstory2requirementoccurrence \<equiv> \<lparr>source = UserStory, target = RequirementOccurence, name = ''causes'', cardinality = OneMany \<rparr>"
abbreviation "functionalsystem2requirementoccurrence \<equiv> \<lparr>source = FunctionalSystem, target = RequirementOccurence, name = ''covers'', cardinality = OneMany \<rparr>"
abbreviation "requirementoccurrence2requirement \<equiv> \<lparr>source = RequirementOccurence, target = Requirement, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "requirementoccurrence2functionoccurrence \<equiv> \<lparr>source = RequirementOccurence, target = FunctionOccurence, name = ''fulfilledBy'', cardinality = OneMany \<rparr>"
abbreviation "functionoccurrence2function \<equiv> \<lparr>source = FunctionOccurence, target = Function, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "functionalpartoccurrence2functionalpart \<equiv> \<lparr>source = FunctionalPartOccurence, target = FunctionalPart, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "componentoccurrence2component \<equiv> \<lparr>source = ComponentOccurence, target = Component, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "functionoccurrence2functionalpartoccurrence \<equiv> \<lparr>source = FunctionOccurence, target = FunctionalPartOccurence, name = ''providedBy'', cardinality = OneMany \<rparr>"
abbreviation "functionalpartoccurrence2componentoccurrence \<equiv> \<lparr>source = FunctionalPartOccurence, target = ComponentOccurence, name = ''implementedBy'', cardinality = OneMany \<rparr>"
abbreviation "requirementoccurrence2functionalpartoccurrence \<equiv> \<lparr>source = RequirementOccurence, target = FunctionalPartOccurence, name = ''fulfilledBy'', cardinality = OneMany \<rparr>"
abbreviation "requirementoccurrence2componentoccurrence \<equiv> \<lparr>source = RequirementOccurence, target = ComponentOccurence, name = ''fulfilledBy'', cardinality = OneMany \<rparr>"
abbreviation "functionoccurrence2functionalsystem \<equiv> \<lparr>source = FunctionOccurence, target = FunctionalSystem, name = ''assignedTo'', cardinality = ManyOne \<rparr>"
abbreviation "functionalpartoccurrence2functionalsystem \<equiv> \<lparr>source = FunctionalPartOccurence, target = FunctionalSystem, name = ''assignedTo'', cardinality = ManyOne \<rparr>"
abbreviation "componentoccurrence2functionalsystem \<equiv> \<lparr>source = ComponentOccurence, target = FunctionalSystem, name = ''assignedTo'', cardinality = ManyOne \<rparr>"
abbreviation "requirement2functiongroup \<equiv> \<lparr>source = Requirement, target = FunctionGroup, name = ''canBeFulfilledBy'', cardinality = OneMany \<rparr>"
abbreviation "requirement2function \<equiv> \<lparr>source = Requirement, target = Function, name = ''canBeFulfilledBy'', cardinality = OneMany \<rparr>"
abbreviation "functiongroup2function \<equiv> \<lparr>source = FunctionGroup, target = Function, name = ''includes'', cardinality = OneMany \<rparr>"
abbreviation "requirement2functionalpart \<equiv> \<lparr>source = Requirement, target = FunctionalPart, name = ''canBeFulfilledBy'', cardinality = OneMany \<rparr>"
abbreviation "functiongroup2functionalpartgroup \<equiv> \<lparr>source = FunctionGroup, target = FunctionalPartGroup, name = ''canBeProvidedBy'', cardinality = OneMany \<rparr>"
abbreviation "function2functionalpart \<equiv> \<lparr>source = Function, target = FunctionalPart, name = ''canBeProvidedBy'', cardinality = OneMany \<rparr>"
abbreviation "functionalpartgroup2functionalpart \<equiv> \<lparr>source = FunctionalPartGroup, target = FunctionalPart, name = ''includes'', cardinality = OneMany \<rparr>"
abbreviation "functionalpart2component \<equiv> \<lparr>source = FunctionalPart, target = Component, name = ''canBeImplementedBy'', cardinality = OneMany \<rparr>"
abbreviation "functionalpartgroup2componentgroup \<equiv> \<lparr>source = FunctionalPartGroup, target = ComponentGroup, name = ''canBeImplementedBy'', cardinality = OneMany \<rparr>"
abbreviation "componentgroup2component \<equiv> \<lparr>source = ComponentGroup, target = Component, name = ''includes'', cardinality = OneMany \<rparr>"
definition ASAOntologyEdges::"edge set"where
"ASAOntologyEdges = {componentproduct2functionalsystem,
                    functionalsystem2userstory, 
                    userstory2requirementoccurrence, 
                    functionalsystem2requirementoccurrence, 
                    requirementoccurrence2requirement, 
                    requirementoccurrence2functionoccurrence, 
                    functionoccurrence2function, 
                    functionalpartoccurrence2functionalpart, 
                    componentoccurrence2component, 
                    functionoccurrence2functionalpartoccurrence, 
                    functionalpartoccurrence2componentoccurrence, 
                    requirementoccurrence2functionalpartoccurrence, 
                    requirementoccurrence2componentoccurrence, 
                    functionoccurrence2functionalsystem, 
                    functionalpartoccurrence2functionalsystem, 
                    componentoccurrence2functionalsystem, 
                    requirement2functiongroup, 
                    requirement2function, 
                    functiongroup2function,
                    requirement2functionalpart, 
                    functiongroup2functionalpartgroup, 
                    function2functionalpart, 
                    functionalpartgroup2functionalpart, 
                    functionalpart2component, 
                    functionalpartgroup2componentgroup, 
                    componentgroup2component}"

global_interpretation ASAOnt: ontology ASAOntologyVertices ASAOntologyEdges
  defines ASAOntology = ASAOnt.Ontology
  by(standard,simp_all add: ASAOntologyVertices_def ASAOntologyEdges_def)
  
end