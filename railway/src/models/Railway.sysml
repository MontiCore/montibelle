package Railway {
  private import ScalarValues::Boolean;

  enum def Section {
    s1; s2; s3; s4; s5; s6; s7;
  }

  attribute def Access_Point {
    enum sect: Section;
    attribute co: Access_Point;
    attribute isOpen: Boolean;
    attribute isGreen: Boolean;
  }

  attribute def Train {
    attribute position: Access_Point;
  }

  attribute def Railway_Network {
    attribute access_points: Access_Point[*];
    attribute trains: Train[*];
  }

  attribute t1: Train {
    ::> position = a21;
  }

  attribute t2: Train {
    ::> position = a73;
  }

  attribute a11 : Access_Point {
    ::> co = a73;
    ::> sect = Section::s1;
    ::> isOpen = true;
    ::> isGreen = false;
  }

  attribute a12 : Access_Point {
    ::> co = a21;
    ::> sect = Section::s1;
    ::> isOpen = true;
    ::> isGreen = false;
  }

  attribute a21 : Access_Point {
    ::> co = a12;
    ::> sect = Section::s2;
    ::> isOpen = true;
    ::> isGreen = false;
  }

  attribute a22 : Access_Point {
    ::> co = a31;
    ::> sect = Section::s2;
    ::> isOpen = true;
    ::> isGreen = false;
  }

  attribute a31 : Access_Point {
    ::> co = a22;
    ::> sect = Section::s3;
    ::> isOpen = true;
    ::> isGreen = false;
  }

  attribute a32 : Access_Point {
    ::> co = a41;
    ::> sect = Section::s3;
    ::> isOpen = true;
    ::> isGreen = false;
  }

  attribute a41 : Access_Point {
    ::> co = a32;
    ::> sect = Section::s4;
    ::> isOpen = true;
    ::> isGreen = false;
  }

  attribute a42 : Access_Point {
    ::> co = a51;
    ::> sect = Section::s4;
    ::> isOpen = true;
    ::> isGreen = false;
  }

  attribute a43 : Access_Point {
    ::> co = a61;
    ::> sect = Section::s4;
    ::> isOpen = false;
    ::> isGreen = false;
  }

  attribute a51 : Access_Point {
    ::> co = a42;
    ::> sect = Section::s5;
    ::> isOpen = true;
    ::> isGreen = false;
  }

  attribute a52 : Access_Point {
    ::> co = a72;
    ::> sect = Section::s5;
    ::> isOpen = true;
    ::> isGreen = false;
  }

  attribute a61 : Access_Point {
    ::> co = a43;
    ::> sect = Section::s6;
    ::> isOpen = true;
    ::> isGreen = false;
  }

  attribute a62 : Access_Point {
    ::> co = a71;
    ::> sect = Section::s6;
    ::> isOpen = true;
    ::> isGreen = false;
  }

  attribute a71 : Access_Point {
    ::> co = a62;
    ::> sect = Section::s7;
    ::> isOpen = false;
    ::> isGreen = false;
  }

  attribute a72 : Access_Point {
    ::> co = a73;
    ::> sect = Section::s7;
    ::> isOpen = true;
    ::> isGreen = false;
  }

  attribute a73 : Access_Point { 
    ::> co = a11;
    ::> sect = Section::s7;
    ::> isOpen = true;
    ::> isGreen = false;
  }

}
