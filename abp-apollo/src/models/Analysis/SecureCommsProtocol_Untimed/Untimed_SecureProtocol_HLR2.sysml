private import ScalarValues::Natural;
private import ScalarValues::Boolean;
private import VerificationLibrary::untimed;

#untimed part def Untimed_SecureProtocol_HLR2 
    specializes Untimed_SecureProtocol_HLR1
{
  part sender: Untimed_Sender_HLR;
  part encrypt1: Untimed_Encrypt1_HLR;
  part eve1: Untimed_Eve1_HLR;
  part decrypt1: Untimed_Decrypt1_HLR;
  part receiver: Untimed_Receiver_HLR;
  part encrypt2: Untimed_Encrypt2_HLR;
  part eve2: Untimed_Eve2_HLR;
  part decrypt2: Untimed_Decrypt2_HLR;

  connect input to sender.input;
  connect sender.output to encrypt1.input;
  connect encrypt1.output to eve1.input;
  connect eve1.output to decrypt1.input;
  connect decrypt1.output to receiver.input;
  connect receiver.output to output;
  connect receiver.control to encrypt2.input;
  connect encrypt2.output to eve2.input;
  connect eve2.output to decrypt2.input;
  connect decrypt2.output to sender.control;
}