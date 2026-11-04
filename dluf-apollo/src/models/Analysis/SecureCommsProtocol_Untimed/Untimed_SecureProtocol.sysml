private import ScalarValues::Natural;
private import ScalarValues::Boolean;
private import ProgramPackage::ApolloProgram::*;
private import VerificationLibrary::untimed;

#untimed part def 'Untimed Protocol' 
    specializes Untimed_SecureProtocol_HLR2, Untimed_SecureProtocol_HLR1
{

  :>> sender: Untimed_Sender_HLR;
  :>> encrypt1: Untimed_Encrypt1_HLR;
  :>> eve1: Untimed_Eve1_HLR;
  :>> decrypt1: Untimed_Decrypt1_HLR;
  :>> receiver: Untimed_Receiver_LLR;
  :>> encrypt2: Untimed_Encrypt2_HLR;
  :>> eve2: Untimed_Eve2_HLR;
  :>> decrypt2: Untimed_Decrypt2_HLR;

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