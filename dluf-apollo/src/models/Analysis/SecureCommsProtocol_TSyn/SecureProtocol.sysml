private import ScalarValues::Natural;
private import ScalarValues::Boolean;
private import ProgramPackage::ApolloProgram::*;
private import VerificationLibrary::tsyn;

#tsyn part def 'Time-Syncronous Protocol' 
    specializes SecureProtocol_HLR2, SecureProtocol_HLR1
{

  ref :>> sender: Sender_HLR
      = apollo11.apollo11MissionSystem.spacecraft.csm.commandModule.sender;
  ref :>> encrypt1: Encrypt1_HLR
      = apollo11.apollo11MissionSystem.spacecraft.csm.commandModule.encrypt;
  ref :>> eve1: Eve1_HLR 
      = apollo11.apollo11MissionContext.mannedSpaceFlightNetwork.eve1;
  ref :>> decrypt1: Decrypt1_HLR
      = apollo11.apollo11MissionContext.missionControl.decrypt;
  ref :>> receiver: Receiver_LLR
      = apollo11.apollo11MissionContext.missionControl.receiver;
  ref :>> encrypt2: Encrypt2_HLR
      = apollo11.apollo11MissionContext.missionControl.encrypt;
  ref :>> eve2: Eve2_HLR
      = apollo11.apollo11MissionContext.mannedSpaceFlightNetwork.eve2;
  ref :>> decrypt2: Decrypt2_HLR
      = apollo11.apollo11MissionSystem.spacecraft.csm.commandModule.decrypt;

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