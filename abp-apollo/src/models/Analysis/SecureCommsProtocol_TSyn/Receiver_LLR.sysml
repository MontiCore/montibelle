private import Streams::SyncStream::**;
private import ScalarValues::**;
private import VerificationLibrary::**;
private import Streams::Eps;

#tsyn part def Receiver_LLR specializes Receiver_HLR {
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
      if input.val == Eps
      do action {
        send Eps to control;
        send Eps to output;
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
        send Eps to output;
      }
      then S;
  }
}