private import VerificationLibrary::untimed;

#untimed part def Untimed_DLDF_HLR2 specializes Untimed_DLDF_HLR1 {
  part scheduler1: Untimed_Scheduler_HLR2 { redefines capacity = cap1; }
  part scheduler2: Untimed_Scheduler_HLR2 { redefines capacity = cap2; }
  part scheduler3: Untimed_Scheduler_HLR2 { redefines capacity = cap3; }
  part scheduler4: Untimed_Scheduler_HLR2 { redefines capacity = cap4; }

  connect input1 to scheduler1.input;
  connect input2 to scheduler2.input;
  connect input3 to scheduler3.input;
  connect input4 to scheduler4.input;

  connect scheduler1.output to output1;
  connect scheduler2.output to output2;
  connect scheduler3.output to output3;
  connect scheduler4.output to output4;
}