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
  requirement def NativeSlotTypes {
    doc /* Slot declarations reuse POO Type objects; ordered normalization ends with every inherited membership check. */
  }
  requirement def CanonicalCells {
    doc /* Live Class validation preserves instance identity and does not normalize canonical cells twice. */
  }
  requirement def Effects {
    doc /* Refused writes preserve cells; external callback effects are not rolled back. */
  }
  requirement def ApplicableMethods {
    doc /* An applicability hook selects distinct eligible methods in its chosen order before combination or execution. */
  }
}
