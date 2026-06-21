-- # Ce test doit passer sans erreur
-- lake env lean lean/test_v38_4_8.lean
import CouretUnification.Logic.TimeBridge.BostConnesMod30Spec
open CouretUnification.Logic.TimeBridge.BostConnesMod30
example : RHClaimed = false := rfl
example : HilbertPolyaClaimed = false := rfl
example : CandidateCClaimed = false := rfl
