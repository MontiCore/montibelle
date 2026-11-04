calc def Schalten {
  in aktuell: Ampelfarben;
  return: Ampelfarben;

  if aktuell == Rot ?
    Gruen
  else
    Rot
}
