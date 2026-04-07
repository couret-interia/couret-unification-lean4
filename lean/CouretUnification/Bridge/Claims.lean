import CouretUnification.Bridge.Status

namespace CouretUnification.Bridge

def noRHClaim : Claim where
  name := "No RH claim"
  status := ClaimStatus.formalized
  description := "This development does not claim a proof of the Riemann Hypothesis."

def finiteCoreStatus : Claim where
  name := "Finite core status"
  status := ClaimStatus.formalized
  description := "The finite mod 30 core is theorem-level Lean content."

def bridgeStatus : Claim where
  name := "Bridge status"
  status := ClaimStatus.roadmap
  description := "The bridge is a structured research program built on top of the finite core."

end CouretUnification.Bridge