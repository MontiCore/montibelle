private import VerificationLibrary::tsyn;
private import Streams::SyncStream::**;
private import Streams::'∞';
private import Streams::Eps;
private import ScalarValues::*;
private import ControlFunctions::**;
private import CollectionFunctions::**;

#tsyn part def TSyn_DLDF_HLR1 {
  port input1: ~Packets;
  port input2: ~Packets;
  port input3: ~Packets;
  port input4: ~Packets;

  port output1: Packets;
  port output2: Packets;
  port output3: Packets;
  port output4: Packets;

  attribute cap1: Natural;
  attribute cap2: Natural;
  attribute cap3: Natural;
  attribute cap4: Natural;

  satisfy requirement NonStarvation {
    attribute input1_history: SyncStream { :>> E: Packet; }
    attribute input2_history: SyncStream { :>> E: Packet; }
    attribute input3_history: SyncStream { :>> E: Packet; }
    attribute input4_history: SyncStream { :>> E: Packet; }
    attribute output1_history: SyncStream { :>> E: Packet; }
    attribute output2_history: SyncStream { :>> E: Packet; }
    attribute output3_history: SyncStream { :>> E: Packet; }
    attribute output4_history: SyncStream { :>> E: Packet; }

    connect input1_history to input1;
    connect input2_history to input2;
    connect input3_history to input3;
    connect input4_history to input4;
    connect output1_history to output1;
    connect output2_history to output2;
    connect output3_history to output3;
    connect output4_history to output4;

    assume constraint InfinitelyLongTimeframe {
      input1_history->len() == '∞' &
      input2_history->len() == '∞' &
      input3_history->len() == '∞' &
      input4_history->len() == '∞'
    }
    assume constraint MessageInEachInterval {
      (all Natural)->forAll {
        in t: Natural;
        input1_history->syncNth(t) != Eps &
        input2_history->syncNth(t) != Eps &
        input3_history->syncNth(t) != Eps &
        input4_history->syncNth(t) != Eps
      }
    }
    assume constraint SizeBelowMaxRate {
      input1_history->values()->forAll { in v: Packet; v.size < cap1 } &
      input2_history->values()->forAll { in v: Packet; v.size < cap2 } &
      input3_history->values()->forAll { in v: Packet; v.size < cap3 } &
      input4_history->values()->forAll { in v: Packet; v.size < cap4 }
    }
    require constraint InfinitelyManyOutputs {
      (output1_history->syncUntimed()->len() == '∞') &
      (output2_history->syncUntimed()->len() == '∞') &
      (output3_history->syncUntimed()->len() == '∞') &
      (output4_history->syncUntimed()->len() == '∞')
    }
  }
}