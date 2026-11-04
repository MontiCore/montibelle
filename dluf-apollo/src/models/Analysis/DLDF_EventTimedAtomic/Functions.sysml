package Functions {

  private import ScalarValues::**;
  private import SequenceFunctions::**;

  calc def takemcap {
    in attribute n: Integer;
    in attribute xs: Packet[*];
    return : Packet[*];

    if (xs->isEmpty()) ? 
      () 
    else if (xs->head().size<=n) ? 
      (x)->add(takemcap(n - xs->head().size, xs->tail())) 
    else
      ()
  }

  calc def lsize {
    in attribute xs: Packet[*];
    return : Natural;

    if (xs->isEmpty()) ? 
      0 
    else
      xs->head().size + lsize(xs->tail()) 
  }
}