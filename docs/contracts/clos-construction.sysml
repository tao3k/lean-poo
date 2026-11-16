package ClosConstruction {
  enum def Phase { allocated; initializing; checked; }
  part def Instance {
    attribute identity : Integer;
    attribute classIdentity : Integer;
    attribute generation : Integer;
    attribute revision : Integer;
    attribute phase : Phase;
  }
  requirement def Allocation {
    doc /* Allocation preserves identity and leaves slots unbound. */
  }
  requirement def Publication {
    doc /* Complete initializer combination and current Class/Slot checks precede return. */
  }
  requirement def Effects {
    doc /* Refused writes preserve cells; external callback effects are not rolled back. */
  }
}
