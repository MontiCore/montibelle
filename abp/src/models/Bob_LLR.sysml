private import Streams::**;
private import ScalarValues::Boolean;

part def Bob_LLR refines Bob_HLR{
  timing delayed;
  port input: ~Data_Bool_Tuples;
  port control: Booleans;
  port output: Data;

  attribute init_ctrl: Data_Bool_Tuple;
    
  #tsyn exhibit state BobAutomaton {
    attribute ctrl: Data_Bool_Tuple;
    state S;
        
    entry action {
      assign ctrl := init_ctrl;
    }
    then S;

    transition
      first S
      if input.val == Eps
      do action {
        send Eps to control.val;
        send Eps to output.val;
      }
      then S;
        
    transition
      first S
      accept input.val 
      if input.val != ctrl 
      do action{
        send input.val.snd to control.val;
        send input.val.fst to output.val;
        assign ctrl := (input.val.fst, not input.val.snd);
      }
      then S;

    transition
      first S
      accept input.val
      if input.val == ctrl 
      do action{
        send input.val.snd to control.val;
        send Eps to output.val;
      }
      then S;
  }
}