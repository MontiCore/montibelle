part def Capacity_HLR3 {
  port input: ~Packets;
  port output: Packets;
  port control: Ctrl;

  attribute cap: nat;

  satisfy requirement NonStarvation {
    assume constraint InfLongTimeframe {
      input.data.len() == INF
    }
    assume constraint SizeBelowMaxCap {
      forall v in input.data.values():
        v.size < cap
    }
    assume constraint ControlMessageSemantics {
      (forall int t:
        (control.data.nth(t+1).len() == input.data.nth(t).len()) ||
        (CtrlEnum.NAK \in control.data.nth(t+1).values()))
      implies
        (forall int t:
          input.data.nth(t).len() > 0)
    }
    require constraint InfManyOutputMessages {
      output.data.untimed().len() == INF
    }
  }
}