private import VerificationLibrary::untimed;
private import VerificationLibrary::Tuple;
private import Streams::UntimedStream::**;
private import ScalarValues::**;

#untimed part def Untimed_Receiver_LLR specializes Receiver_HLR {
  attribute init_ctrl: Tuple { 
    redefines fst: Natural; 
    redefines snd: Boolean; 
  }
    
  exhibit state {
    attribute ctrl: Tuple { 
      redefines fst: Natural; 
      redefines snd: Boolean; 
    }
    state S;
        
    entry action {
      assign ctrl := init_ctrl;
    }
    then S;

    transition
      first S
      if input.val != ctrl 
      do action{
        send input.val.snd to control;
        send input.val.fst to output;
        assign ctrl := (input.val.fst, not input.val.snd);
      }
      then S;

    transition
      first S
      if input.val == ctrl 
      do action{
        send input.val.snd to control;
      }
      then S;
  }
}