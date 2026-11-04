theory dreaminstance
  imports ClassDiagramAnalyses
begin



abbreviation "Dream \<equiv>  (''Dream'' ,''Component (Product)'')"

abbreviation "Avionics \<equiv>  (''Avionics'', ''FunctionalSystem'')"

abbreviation "SecureControl \<equiv>  (''SecureControl'' ,''UserStory'')"

abbreviation "SecureLinkReqOccurence \<equiv>  (''SecureLinkReqOccurence'', ''RequirementOccurence'')"

abbreviation "SecureLinkOccurence \<equiv>  (''SecureLinkOccurence'', ''FunctionOccurence'')"

abbreviation "Scheduler1Occurence \<equiv>  (''Scheduler1Occurence'' ,''FunctionalPartOccurence'')"
abbreviation "Scheduler2Occurence \<equiv>  (''Scheduler2Occurence'' ,''FunctionalPartOccurence'')"
abbreviation "Scheduler3Occurence \<equiv>  (''Scheduler3Occurence'' ,''FunctionalPartOccurence'')"
abbreviation "Scheduler4Occurence \<equiv>  (''Scheduler4Occurence'' ,''FunctionalPartOccurence'')"

abbreviation "Buffer1Occurence \<equiv>  (''Buffer1Occurence'' ,''ComponentOccurence'')"
abbreviation "Buffer2Occurence \<equiv>  (''Buffer2Occurence'' ,''ComponentOccurence'')"
abbreviation "Buffer3Occurence \<equiv>  (''Buffer3Occurence'' ,''ComponentOccurence'')"
abbreviation "Buffer4Occurence \<equiv>  (''Buffer4Occurence'' ,''ComponentOccurence'')"
abbreviation "Capacity1Occurence \<equiv>  (''Capacity1Occurence'' ,''ComponentOccurence'')"
abbreviation "Capacity2Occurence \<equiv>  (''Capacity2Occurence'' ,''ComponentOccurence'')"
abbreviation "Capacity3Occurence \<equiv>  (''Capacity3Occurence'' ,''ComponentOccurence'')"
abbreviation "Capacity4Occurence \<equiv>  (''Capacity4Occurence'' ,''ComponentOccurence'')"


abbreviation "SecureLinkReq \<equiv>  (''SecureLinkReq'', ''Requirement'')"

abbreviation "SecureLinkFunctionGroup \<equiv>  (''SecureLinkFunctionGroup'', ''FunctionGroup'')"

abbreviation "SecureLinkFunction \<equiv>  (''SecureLinkFunction'', ''Function'')"

abbreviation "SchedulerFunctionGroup \<equiv>  (''SchedulerFunctionGroup'', ''FunctionalPartGroup'')"

abbreviation "SchedulerFunction \<equiv>  (''SchedulerFunction'' ,''FunctionalPart'')"

abbreviation "SchedulerComponentGroup \<equiv>  (''SchedulerComponentGroup'', ''ComponentGroup'')"

abbreviation "BufferComponent \<equiv>  (''BufferComponent'', ''Component'')"
abbreviation "CapacityComponent \<equiv>  (''CapacityComponent'', ''Component'')"




definition DreamVertices::"vertex set"where
"DreamVertices = {Dream,
                  Avionics,
                  SecureControl,
                  SecureLinkReqOccurence,
                  SecureLinkOccurence,
                  Scheduler1Occurence, 
                  Scheduler2Occurence, 
                  Scheduler3Occurence, 
                  Scheduler4Occurence, 
                  Buffer1Occurence, 
                  Buffer2Occurence, 
                  Buffer3Occurence, 
                  Buffer4Occurence, 
                  Capacity1Occurence, 
                  Capacity2Occurence, 
                  Capacity3Occurence, 
                  Capacity4Occurence,
                  SecureLinkReq, 
                  SecureLinkFunctionGroup,
                  SecureLinkFunction,
                  SchedulerFunctionGroup,
                  SchedulerComponentGroup,
                  SchedulerFunction,
                  BufferComponent,
                  CapacityComponent}"



abbreviation "dream2avionics \<equiv> \<lparr>source = Dream, target = Avionics, name = ''isA'', cardinality = OneOne \<rparr>"

abbreviation "avionics2securecontrol \<equiv> \<lparr>source = Avionics, target = SecureControl, name = ''covers'', cardinality = OneOne \<rparr>"

abbreviation "securecontrol2securelinkreqoccurence \<equiv> \<lparr>source = SecureControl, target = SecureLinkReqOccurence, name = ''causes'', cardinality = OneOne \<rparr>"

abbreviation "avionics2securelinkreqoccurence \<equiv> \<lparr>source = Avionics, target = SecureLinkReqOccurence, name = ''covers'', cardinality = OneOne \<rparr>"

abbreviation "securelinkreqoccurence2securelinkreq \<equiv> \<lparr>source = SecureLinkReqOccurence, target = SecureLinkReq, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "securelinkoccurence2securelinkfunction \<equiv> \<lparr>source = SecureLinkOccurence, target = SecureLinkFunction, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "scheduler1occurence2schedulerfunction \<equiv> \<lparr>source = Scheduler1Occurence, target = SchedulerFunction, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "scheduler2occurence2schedulerfunction \<equiv> \<lparr>source = Scheduler2Occurence, target = SchedulerFunction, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "scheduler3occurence2schedulerfunction \<equiv> \<lparr>source = Scheduler3Occurence, target = SchedulerFunction, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "scheduler4occurence2schedulerfunction \<equiv> \<lparr>source = Scheduler4Occurence, target = SchedulerFunction, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "buffer1occurence2buffercomponent \<equiv> \<lparr>source = Buffer1Occurence, target = BufferComponent, name = ''is'', cardinality = OneOne \<rparr>"

abbreviation "buffer1occurence2capacitycomponent \<equiv> \<lparr>source = Buffer1Occurence, target = CapacityComponent, name = ''is'', cardinality = OneOne \<rparr>"

abbreviation "buffer2occurence2buffercomponent \<equiv> \<lparr>source = Buffer2Occurence, target = BufferComponent, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "buffer3occurence2buffercomponent \<equiv> \<lparr>source = Buffer3Occurence, target = BufferComponent, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "buffer4occurence2buffercomponent \<equiv> \<lparr>source = Buffer4Occurence, target = BufferComponent, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "capacity1occurence2capacitycomponent \<equiv> \<lparr>source = Capacity1Occurence, target = CapacityComponent, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "capacity2occurence2capacitycomponent \<equiv> \<lparr>source = Capacity2Occurence, target = CapacityComponent, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "capacity3occurence2capacitycomponent \<equiv> \<lparr>source = Capacity3Occurence, target = CapacityComponent, name = ''is'', cardinality = OneOne \<rparr>"
abbreviation "capacity4occurence2capacitycomponent \<equiv> \<lparr>source = Capacity4Occurence, target = CapacityComponent, name = ''is'', cardinality = OneOne \<rparr>"


abbreviation "securelinkreqoccurence2securelinkoccurence \<equiv> \<lparr>source = SecureLinkReqOccurence, target = SecureLinkOccurence, name = ''fulfilledBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkreqoccurence2scheduler1occurence \<equiv> \<lparr>source = SecureLinkReqOccurence, target = Scheduler1Occurence, name = ''fulfilledBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkreqoccurence2scheduler2occurence \<equiv> \<lparr>source = SecureLinkReqOccurence, target = Scheduler2Occurence, name = ''fulfilledBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkreqoccurence2scheduler3occurence \<equiv> \<lparr>source = SecureLinkReqOccurence, target = Scheduler3Occurence, name = ''fulfilledBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkreqoccurence2scheduler4occurence \<equiv> \<lparr>source = SecureLinkReqOccurence, target = Scheduler4Occurence, name = ''fulfilledBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkreqoccurence2buffer1occurence \<equiv> \<lparr>source = SecureLinkReqOccurence, target = Buffer1Occurence, name = ''fulfilledBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkreqoccurence2buffer2occurence \<equiv> \<lparr>source = SecureLinkReqOccurence, target = Buffer2Occurence, name = ''fulfilledBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkreqoccurence2buffer3occurence \<equiv> \<lparr>source = SecureLinkReqOccurence, target = Buffer3Occurence, name = ''fulfilledBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkreqoccurence2buffer4occurence \<equiv> \<lparr>source = SecureLinkReqOccurence, target = Buffer4Occurence, name = ''fulfilledBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkreqoccurence2capacity1occurence \<equiv> \<lparr>source = SecureLinkReqOccurence, target = Capacity1Occurence, name = ''fulfilledBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkreqoccurence2capacity2occurence \<equiv> \<lparr>source = SecureLinkReqOccurence, target = Capacity2Occurence, name = ''fulfilledBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkreqoccurence2capacity3occurence \<equiv> \<lparr>source = SecureLinkReqOccurence, target = Capacity3Occurence, name = ''fulfilledBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkreqoccurence2capacity4occurence \<equiv> \<lparr>source = SecureLinkReqOccurence, target = Capacity4Occurence, name = ''fulfilledBy'', cardinality = OneOne \<rparr>"

abbreviation "securelinkoccurence2scheduler1occurence \<equiv> \<lparr>source = SecureLinkOccurence, target = Scheduler1Occurence, name = ''providedBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkoccurence2scheduler2occurence \<equiv> \<lparr>source = SecureLinkOccurence, target = Scheduler2Occurence, name = ''providedBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkoccurence2scheduler3occurence \<equiv> \<lparr>source = SecureLinkOccurence, target = Scheduler3Occurence, name = ''providedBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkoccurence2scheduler4occurence \<equiv> \<lparr>source = SecureLinkOccurence, target = Scheduler4Occurence, name = ''providedBy'', cardinality = OneOne \<rparr>"

abbreviation "scheduler1occurence2buffer1component \<equiv> \<lparr>source = Scheduler1Occurence, target = Buffer1Occurence, name = ''implementedBy'', cardinality = OneOne \<rparr>"
abbreviation "scheduler1occurence2capacity1component \<equiv> \<lparr>source = Scheduler1Occurence, target = Capacity1Occurence, name = ''implementedBy'', cardinality = OneOne \<rparr>"
abbreviation "scheduler2occurence2buffer2component \<equiv> \<lparr>source = Scheduler2Occurence, target = Buffer2Occurence, name = ''implementedBy'', cardinality = OneOne \<rparr>"
abbreviation "scheduler2occurence2capacity2component \<equiv> \<lparr>source = Scheduler2Occurence, target = Capacity2Occurence, name = ''implementedBy'', cardinality = OneOne \<rparr>"
abbreviation "scheduler3occurence2buffer3component \<equiv> \<lparr>source = Scheduler3Occurence, target = Buffer3Occurence, name = ''implementedBy'', cardinality = OneOne \<rparr>"
abbreviation "scheduler3occurence2capacity3component \<equiv> \<lparr>source = Scheduler3Occurence, target = Capacity3Occurence, name = ''implementedBy'', cardinality = OneOne \<rparr>"
abbreviation "scheduler4occurence2buffer4component \<equiv> \<lparr>source = Scheduler4Occurence, target = Buffer4Occurence, name = ''implementedBy'', cardinality = OneOne \<rparr>"
abbreviation "scheduler4occurence2capacity4component \<equiv> \<lparr>source = Scheduler4Occurence, target = Capacity4Occurence, name = ''implementedBy'', cardinality = OneOne \<rparr>"

abbreviation "securelinkoccurence2avionics \<equiv> \<lparr>source = SecureLinkOccurence, target = Avionics, name = ''assignedTo'', cardinality = OneOne \<rparr>"
abbreviation "scheduler1occurence2avionics \<equiv> \<lparr>source = Scheduler1Occurence, target = Avionics, name = ''assignedTo'', cardinality = OneOne \<rparr>"
abbreviation "scheduler2occurence2avionics \<equiv> \<lparr>source = Scheduler2Occurence, target = Avionics, name = ''assignedTo'', cardinality = OneOne \<rparr>"
abbreviation "scheduler3occurence2avionics \<equiv> \<lparr>source = Scheduler3Occurence, target = Avionics, name = ''assignedTo'', cardinality = OneOne \<rparr>"
abbreviation "scheduler4occurence2avionics \<equiv> \<lparr>source = Scheduler4Occurence, target = Avionics, name = ''assignedTo'', cardinality = OneOne \<rparr>"
abbreviation "buffer1occurence2avionics \<equiv> \<lparr>source = Buffer1Occurence, target = Avionics, name = ''assignedTo'', cardinality = OneOne \<rparr>"
abbreviation "buffer2occurence2avionics \<equiv> \<lparr>source = Buffer2Occurence, target = Avionics, name = ''assignedTo'', cardinality = OneOne \<rparr>"
abbreviation "buffer3occurence2avionics \<equiv> \<lparr>source = Buffer3Occurence, target = Avionics, name = ''assignedTo'', cardinality = OneOne \<rparr>"
abbreviation "buffer4occurence2avionics \<equiv> \<lparr>source = Buffer4Occurence, target = Avionics, name = ''assignedTo'', cardinality = OneOne \<rparr>"
abbreviation "capacity1occurence2avionics \<equiv> \<lparr>source = Capacity1Occurence, target = Avionics, name = ''assignedTo'', cardinality = OneOne \<rparr>"
abbreviation "capacity2occurence2avionics \<equiv> \<lparr>source = Capacity2Occurence, target = Avionics, name = ''assignedTo'', cardinality = OneOne \<rparr>"
abbreviation "capacity3occurence2avionics \<equiv> \<lparr>source = Capacity3Occurence, target = Avionics, name = ''assignedTo'', cardinality = OneOne \<rparr>"
abbreviation "capacity4occurence2avionics \<equiv> \<lparr>source = Capacity4Occurence, target = Avionics, name = ''assignedTo'', cardinality = OneOne \<rparr>"

abbreviation "securelinkreq2securelinkfunctiongroup \<equiv> \<lparr>source = SecureLinkReq, target = SecureLinkFunctionGroup, name = ''canBeFulfilledBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkreq2securelinkfunction \<equiv> \<lparr>source = SecureLinkReq, target = SecureLinkFunction, name = ''canBeFulfilledBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkreq2schedulerfunction \<equiv> \<lparr>source = SecureLinkReq, target = SchedulerFunction, name = ''canBeFulfilledBy'', cardinality = OneOne \<rparr>"

abbreviation "securelinkfunctiongroup2securelinkfunction \<equiv> \<lparr>source = SecureLinkFunctionGroup, target = SecureLinkFunction, name = ''includes'', cardinality = OneOne \<rparr>"
abbreviation "schedulerfunctiongroup2schedulerfunction \<equiv> \<lparr>source = SchedulerFunctionGroup, target = SchedulerFunction, name = ''includes'', cardinality = OneOne \<rparr>"


abbreviation "securelinkfunctiongroup2schedulerfunctiongroup \<equiv> \<lparr>source = SecureLinkFunctionGroup, target = SchedulerFunctionGroup, name = ''canBeProvidedBy'', cardinality = OneOne \<rparr>"
abbreviation "securelinkfunction2schedulerfunction \<equiv> \<lparr>source = SecureLinkFunction, target = SchedulerFunction, name = ''canBeProvidedBy'', cardinality = OneOne \<rparr>"

abbreviation "schedulerfunctiongroup2schedulercomponentgroup \<equiv> \<lparr>source = SchedulerFunctionGroup, target = SchedulerComponentGroup, name = ''canBeImplementedBy'', cardinality = OneOne \<rparr>"
abbreviation "schedulerfunction2buffercomponent \<equiv> \<lparr>source = SchedulerFunction, target = BufferComponent, name = ''canBeImplementedBy'', cardinality = OneOne \<rparr>"
abbreviation "schedulerfunction2capacitycomponent \<equiv> \<lparr>source = SchedulerFunction, target = CapacityComponent, name = ''canBeImplementedBy'', cardinality = OneOne \<rparr>"


definition DreamEdges::"edge set"where
"DreamEdges = {dream2avionics,
                    avionics2securecontrol, 
                    securecontrol2securelinkreqoccurence, 
                    avionics2securelinkreqoccurence, 
                    securelinkreqoccurence2securelinkreq, 
                    securelinkoccurence2securelinkfunction, 
                    scheduler1occurence2schedulerfunction, 
                    scheduler2occurence2schedulerfunction, 
                    scheduler3occurence2schedulerfunction, 
                    scheduler4occurence2schedulerfunction, 
                    buffer1occurence2buffercomponent, 
                    buffer2occurence2buffercomponent, 
                    buffer3occurence2buffercomponent, 
                    buffer4occurence2buffercomponent, 
                    capacity1occurence2capacitycomponent, 
                    capacity2occurence2capacitycomponent, 
                    capacity3occurence2capacitycomponent, 
                    capacity4occurence2capacitycomponent, 
                    securelinkreqoccurence2securelinkoccurence,
                    securelinkreqoccurence2scheduler1occurence, 
                    securelinkreqoccurence2scheduler2occurence, 
                    securelinkreqoccurence2scheduler3occurence, 
                    securelinkreqoccurence2scheduler4occurence, 
                    securelinkreqoccurence2buffer1occurence, 
                    securelinkreqoccurence2buffer2occurence, 
                    securelinkreqoccurence2buffer3occurence, 
                    securelinkreqoccurence2buffer4occurence, 
                    securelinkreqoccurence2capacity1occurence, 
                    securelinkreqoccurence2capacity2occurence, 
                    securelinkreqoccurence2capacity3occurence, 
                    securelinkreqoccurence2capacity4occurence, 
                    securelinkoccurence2scheduler1occurence, 
                    securelinkoccurence2scheduler2occurence, 
                    securelinkoccurence2scheduler3occurence, 
                    securelinkoccurence2scheduler4occurence, 
                    scheduler1occurence2buffer1component, 
                    scheduler2occurence2buffer2component,
                    scheduler3occurence2buffer3component, 
                    scheduler4occurence2buffer4component, 
                    scheduler1occurence2capacity1component, 
                    scheduler2occurence2capacity2component, 
                    scheduler3occurence2capacity3component, 
                    scheduler4occurence2capacity4component, 
                    securelinkoccurence2avionics, 
                    scheduler1occurence2avionics, 
                    scheduler2occurence2avionics, 
                    scheduler3occurence2avionics, 
                    scheduler4occurence2avionics, 
                    buffer1occurence2avionics, 
                    buffer2occurence2avionics, 
                    buffer3occurence2avionics, 
                    buffer4occurence2avionics, 
                    capacity1occurence2avionics, 
                    capacity2occurence2avionics, 
                    capacity3occurence2avionics,
                    capacity4occurence2avionics, 
                    securelinkreq2securelinkfunctiongroup, 
                    securelinkreq2securelinkfunction, 
                    securelinkreq2schedulerfunction, 
                    securelinkfunctiongroup2securelinkfunction, 
                    schedulerfunctiongroup2schedulerfunction, 
                    securelinkfunctiongroup2schedulerfunctiongroup, 
                    securelinkfunction2schedulerfunction, 
                    schedulerfunctiongroup2schedulercomponentgroup, 
                    schedulerfunction2buffercomponent, 
                    schedulerfunction2capacitycomponent}"

global_interpretation DreamInst: ontology DreamVertices DreamEdges
  defines DreamInstance = DreamInst.Ontology
  apply(standard)
  apply (simp add: DreamVertices_def)
  apply (simp add: DreamEdges_def)
  apply eval
  apply eval
  done

end