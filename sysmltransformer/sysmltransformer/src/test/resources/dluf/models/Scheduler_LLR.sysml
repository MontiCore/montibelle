part def Scheduler_LLR specializes Scheduler_HLR3, Scheduler_HLR2 {
  port input: ~Packets;
  port output: Packets;

  attribute capacity: nat;

  part buffer: Buffer_LLR;
  part capacityComponent: Capacity_LLR { attribute cap = capacity; }

  connect input to buffer.input;
  connect buffer.output to capacityComponent.input;
  connect capacityComponent.control to buffer.control;
  connect capacityComponent.output to output;
}
