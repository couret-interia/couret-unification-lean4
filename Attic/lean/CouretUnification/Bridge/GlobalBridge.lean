namespace CouretUnification.Bridge

inductive ComponentStatus where
  | closed | constructed | conditional | open_
  deriving DecidableEq, Repr

structure GlobalBridgeStatus where
  finiteCore : ComponentStatus
  characterDecomp : ComponentStatus
  primorialTower : ComponentStatus
  eulerPartial : ComponentStatus
  limitOperator : ComponentStatus
  traceFormula : ComponentStatus
  zeroMatching : ComponentStatus

def currentGlobalStatus : GlobalBridgeStatus where
  finiteCore := .closed
  characterDecomp := .constructed
  primorialTower := .constructed
  eulerPartial := .constructed
  limitOperator := .conditional
  traceFormula := .open_
  zeroMatching := .open_

theorem bridge_not_closed :
    currentGlobalStatus.traceFormula = .open_ ∧
    currentGlobalStatus.zeroMatching = .open_ := ⟨rfl, rfl⟩

def RHClaimed : Bool := false
theorem rh_not_claimed : RHClaimed = false := rfl

end CouretUnification.Bridge
