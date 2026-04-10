import CouretUnification.Logic.H3.Lock2Conditional

namespace CouretUnification.Logic.H3

axiom spectral_id_to_zero_matching (hDet : Det2IdentifiesXi) : ZeroMatching

def RHClaimed : Bool := false
theorem rh_not_claimed : RHClaimed = false := rfl

end CouretUnification.Logic.H3
