part def Lambdas {
  port i:  Booleans;
  port o: ~Booleans;

  exhibit state behavior {

    calc Map {
      in attribute b: boolean;
      return: boolean;

      b
    }

    state S;

    transition
      first S
      accept i.val
      if true
      do action {
        assign Map := { attribute b: boolean; return: boolean; !b };
      }
      then S;
  }
}
