part def LambdasAddition {
  port i:  Nats;
  port o: ~Nats;

  exhibit state behavior {

    calc Map {
      in attribute i: nat;
      in attribute j: nat;
      return: nat;

      i
    }

    state S;

    transition
      first S
      accept i.val
      if true
      do action {
        assign Map := {in attribute i: nat; in attribute j: nat; return: nat; i+j};
      }
      then S;
  }
}
