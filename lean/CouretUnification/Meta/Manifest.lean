namespace CouretUnification.Meta

structure PackageManifest where
  modules : Option Nat
  substantiveTheorems : Option Nat
  totalDeclarations : Option Nat
  axioms : Nat
  sorryCount : Nat
  coreClean : Bool
  note : String
  deriving Repr

def currentManifest : PackageManifest :=
  { modules := none
  , substantiveTheorems := none
  , totalDeclarations := none
  , axioms := 0
  , sorryCount := 0
  , coreClean := true
  , note := "Counts pending explicit audit/generation on Lean 4.29.0." }

end CouretUnification.Meta