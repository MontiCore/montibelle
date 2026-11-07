private import VerificationLibrary::tsyn;

#tsyn part def TSyn_DLDF_HLR3 specializes TSyn_DLDF_HLR2, TSyn_DLDF_HLR1 {
  redefines scheduler1: TSyn_Scheduler_HLR3 { :>> scheduler1.capacity = cap1; }
  redefines scheduler2: TSyn_Scheduler_HLR3 { :>> scheduler2.capacity = cap2; }
  redefines scheduler3: TSyn_Scheduler_HLR3 { :>> scheduler3.capacity = cap3; }
  redefines scheduler4: TSyn_Scheduler_HLR3 { :>> scheduler4.capacity = cap4; }

  connect input1 to scheduler1.input;
  connect input2 to scheduler2.input;
  connect input3 to scheduler3.input;
  connect input4 to scheduler4.input;

  connect scheduler1.output to output1;
  connect scheduler2.output to output2;
  connect scheduler3.output to output3;
  connect scheduler4.output to output4;
}