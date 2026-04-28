namespace CouretUnification.Meta

inductive AuditTier
  | substantive
  | structural
  | warning
  deriving Repr, DecidableEq

structure AuditItem where
  label : String
  tier : AuditTier
  note : String
  deriving Repr

def audit : List AuditItem :=
  [ { label := "Core clean"
    , tier := .substantive
    , note := "Core has no axioms, no sorry, no fake proofs." }
  , { label := "Bridge discipline"
    , tier := .structural
    , note := "No Prop := True; statuses separated from proofs." }
  ]

end CouretUnification.Meta