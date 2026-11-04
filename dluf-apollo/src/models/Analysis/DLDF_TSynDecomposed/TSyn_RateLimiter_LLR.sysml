private import VerificationLibrary::**;
private import ScalarValues::**;
private import SequenceFunctions::**;
private import Streams::**;

#tsyn part def TSyn_RateLimiter_LLR specializes TSyn_RateLimiter_HLR3 {
  port in2: ~Confirmations;

  exhibit state {
    attribute c: Natural;
    attribute timer: Natural;
    entry action {
      assign c := cap;
      assign timer := 10;
    }
    then Send;

    state Send;
    state Block;

    transition
      first Send
      if c >= input.data.size
      do action {
        send CtrlEnum::ACK to control;
        send input.data to output;
        assign c := c-input.data.size;
      }
      then Send;

    transition
      first Send
      if c < input.data.size
      do action { send CtrlEnum::NAK to control; }
      then Block;

    transition
      first Block
      if input.data != Eps
      then Block;

    transition
      first Send
      if input.data == Eps & timer == 0
      do action { 
        assign c := cap; 
        assign timer := 10;
      }
      then Send;

    transition
      first Block
      if input.data == Eps & timer == 0
      do action { 
        assign c := cap; 
        assign timer := 10;
      }
      then Send;
    
    transition
      first Send
      if input.data == Eps & timer > 0
      do action {
        assign timer := timer-1;
      }
      then Send;

    transition
      first Block
      if input.data == Eps & timer > 0
      do action {
        assign timer := timer-1;
      }
      then Send;
  }
}
