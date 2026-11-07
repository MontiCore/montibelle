part def Scheduler_HLR2 {
  port input: ~Packets;
  port output: Packets;

  attribute capacity: nat;

  satisfy requirement NonStarvation {
    assume constraint InfLongTimeframe {
      input.data.len() == INF
    }
    assume constraint MessageInEachInterval {
      forall int t:
        input.data.nth(t).len() > 0
    }
    assume constraint SizeBelowMaxCap {
      forall v in input.data.values():
        v.size < capacity
    }
    require constraint InfManyOutputMessages {
      output.data.untimed().len() == INF
    }
  }
}