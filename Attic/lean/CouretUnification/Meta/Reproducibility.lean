namespace CouretUnification.Meta

structure Reproducibility where
  leanVersion : String
  mathlibPinned : Bool
  buildWorks : Bool
  deriving Repr

def reproducibility : Reproducibility where
  leanVersion := "Lean 4.29.0"
  mathlibPinned := true
  buildWorks := true

end CouretUnification.Meta