package Signals {
  private import ScalarValues::Boolean;
  private import Railway::*;

  attribute def Enters {
    attribute train: Train;
    attribute access: Access_Point;
  }

  attribute def OpenUp {
    attribute a: Access_Point;
    attribute b: Access_Point;
  }

  attribute def SetColor {
    attribute access: Access_Point;
    attribute b: Boolean;
  }

  enum def Reject {
    Reject;
  }
}