private import VerificationLibrary::untimed;
private import ScalarValues::**;
private import SequenceFunctions::**;
private import Streams::**;

#untimed part def Untimed_RateLimiter_LLR 
    specializes Untimed_RateLimiter_HLR3 
{
  exhibit state {
    entry action {
      assign c := cap;
    }
    then Send;
    state Send;
    state Block;
    attribute c: Natural;

    transition
      first Send
      accept p: Packet via input
      if c >= p.size
      do action {
        send CtrlEnum::ACK to control;
        send p to output;
        assign c := c-p.size;
      }
      then Send;

    transition
      first Send
      accept p: Packet via input
      if c < input.data.size
      do action { send CtrlEnum::NAK to control; }
      then Block;

    transition
      first Block
      accept p: Packet via input
      then Block;

    transition
      first Send
      accept p: Packet via input
      do action { assign c := cap; }
      then Send;

    transition
      first Block
      accept p: Packet via input
      do action { assign c := cap; }
      then Send;
  }
}