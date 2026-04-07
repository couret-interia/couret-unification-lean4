import CouretUnification.Bridge.Status

namespace CouretUnification.Bridge

structure UnificationState where
  characterWeighted : ClaimStatus
  weakCoupling : ClaimStatus
  strongCoupling : ClaimStatus
  spectralCoupling : ClaimStatus
  deriving Repr

def currentUnification : UnificationState where
  characterWeighted := ClaimStatus.constructed
  weakCoupling := ClaimStatus.open_
  strongCoupling := ClaimStatus.open_
  spectralCoupling := ClaimStatus.open_

theorem weakCoupling_open :
    currentUnification.weakCoupling = ClaimStatus.open_ := by
  rfl

theorem strongCoupling_open :
    currentUnification.strongCoupling = ClaimStatus.open_ := by
  rfl

theorem spectralCoupling_open :
    currentUnification.spectralCoupling = ClaimStatus.open_ := by
  rfl

end CouretUnification.Bridge