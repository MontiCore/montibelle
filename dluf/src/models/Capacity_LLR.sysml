part def Capacity_LLR
  specializes Capacity_HLR3 
{
  port input: ~Packets;
  port output: Packets;
  port control: Ctrl;

  attribute cap: nat;

  exhibit state CapacityAutomaton {
    entry action {
      assign c := cap;
    }
    then Send;
    state Send;
    state Block;
    attribute c: nat;

    transition
      first Send
      accept input.data
      if c >= input.data.size
      do action {
        send CtrlEnum.ACK to control.data;
        send input.data to output.data;
        assign c := c-input.data.size;
      }
      then Send;

    transition
      first Send
      accept input.data
      if c < input.data.size
      do action { send CtrlEnum.NAK to control.data; }
      then Block;

    transition
      first Block
      accept input.data
      then Block;

    transition
      first Send
      accept Tick
      do action { assign c := cap; }
      then Send;

    transition
      first Block
      accept Tick
      do action { assign c := cap; }
      then Send;
  }
}