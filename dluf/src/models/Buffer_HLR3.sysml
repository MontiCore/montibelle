part def Buffer_HLR3 {
  timing instant;
  
  port input: ~Packets;
  port control: ~Ctrl;
  port output: Packets;

  satisfy requirement NonStarvation {
    assume constraint InfLongTimeframe {
      input.data.len() == INF && control.data.len() == INF
    }
    assume constraint MessageInEachInterval {
      forall int t:
        input.data.nth(t).len() > 0
    }
    require constraint alwaysTransmit {
      (forall int t:
        (control.data.nth(t+1).len() == output.data.nth(t).len()) ||
        (CtrlEnum.NAK \in control.data.nth(t+1).values()))
      implies
        (forall int t:
          output.data.nth(t).len() > 0)
    }

    require constraint outputSubsetInput {
      output.data.values() \subseteq input.data.values()
    }
  }

}
