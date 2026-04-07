namespace CouretUnification.Bridge

inductive ClaimStatus
  | formalized
  | constructed
  | conditional
  | open_
  | roadmap
  | program
  deriving Repr, DecidableEq

structure Claim where
  name : String
  status : ClaimStatus
  description : String
  deriving Repr

end CouretUnification.Bridge