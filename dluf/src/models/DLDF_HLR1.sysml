part def DLDF_HLR1 {
  port input1: ~Packets;
  port input2: ~Packets;
  port input3: ~Packets;
  port input4: ~Packets;

  port output1: Packets;
  port output2: Packets;
  port output3: Packets;
  port output4: Packets;

  attribute cap1: nat;
  attribute cap2: nat;
  attribute cap3: nat;
  attribute cap4: nat;

  satisfy requirement NonStarvation {
    assume constraint InfinitelyLongTimeframe {
      input1.data.len() == INF &&
      input2.data.len() == INF &&
      input3.data.len() == INF &&
      input4.data.len() == INF
    }
    assume constraint MessageInEachInterval {
      forall int t:
        input1.data.nth(t).len() > 0 &&
        input2.data.nth(t).len() > 0 &&
        input3.data.nth(t).len() > 0 &&
        input4.data.nth(t).len() > 0
    }
    assume constraint SizeBelowMaxCapacity {
      (forall v in input1.data.values(): v.size < cap1) &&
      (forall v in input2.data.values(): v.size < cap2) &&
      (forall v in input3.data.values(): v.size < cap3) &&
      (forall v in input4.data.values(): v.size < cap4)
    }
    require constraint InfinitelyManyOutputs {
      (output1.data.untimed().len() == INF) &&
      (output2.data.untimed().len() == INF) &&
      (output3.data.untimed().len() == INF) &&
      (output4.data.untimed().len() == INF)
    }
  }
}