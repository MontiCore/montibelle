private import ScalarValues::Natural;
private import ScalarValues::Boolean;
private import VerificationLibrary::tsyn;

#tsyn part def SecureProtocol_HLR2 specializes SecureProtocol_HLR1 {
  part sender: Sender_HLR;
  part encrypt1: Encrypt1_HLR;
  part eve1: Eve1_HLR;
  part decrypt1: Decrypt1_HLR;
  part receiver: Receiver_HLR;
  part encrypt2: Encrypt2_HLR;
  part eve2: Eve2_HLR;
  part decrypt2: Decrypt2_HLR;

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