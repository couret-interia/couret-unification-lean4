/-
  Couret-Unification — v35.9.1
  Logic/ExplicitFormula/ExplicitFormulaBridge.lean

  Objet : LE MIROIR ARITHMÉTICO-SPECTRAL — voûte commutative 4 sides.

  Statut     : Frozen-eligible (0 sorry, 0 axiome local, 0 constante analytique)
  Layer      : Logic.ExplicitFormula
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0
  axiomCount             : 0

  Changement v35.9.0 → v35.9.1 :
    La voûte utilise désormais uniformément les `FormulaSide` du
    module `TraceObject`, et les certificats d'égalité sont des
    `SideEqualsTrace` réifiables.

  Pour Bernard.
-/

import CouretUnification.Logic.ExplicitFormula.TestPair
import CouretUnification.Logic.ExplicitFormula.TraceObject

namespace CouretUnification.Logic.ExplicitFormula

/-- Certificat de la formule explicite.

    La voûte demande :
      PrimeSide + ArchimedeanSide = TraceObject
      ZeroSide                    = TraceObject
      Det2Side                    = TraceObject

    Ces égalités sont des champs explicites — toute preuve de RH qui
    emprunte ce chemin doit les avoir toutes quatre instanciées sans
    sorry. -/
structure ExplicitFormulaBridge where
  primeSide       : FormulaSide
  archimedeanSide : FormulaSide
  zeroSide        : FormulaSide
  det2Side        : FormulaSide
  trace           : TraceObject
  /-- Égalité 1 : PrimeSide + ArchimedeanSide = Trace. -/
  arith_plus_arch_eq_trace :
    ∀ φ : TestPair,
      primeSide.value φ + archimedeanSide.value φ = trace.value φ
  /-- Égalité 2 : ZeroSide = Trace. -/
  zero_eq_trace :
    ∀ φ : TestPair, zeroSide.value φ = trace.value φ
  /-- Égalité 3 : Det2Side = Trace. -/
  det2_eq_trace :
    ∀ φ : TestPair, det2Side.value φ = trace.value φ

/-- Admissibilité globale du bridge. -/
def ExplicitFormulaAdmissible (B : ExplicitFormulaBridge) : Prop :=
  (∀ φ : TestPair,
      B.primeSide.value φ + B.archimedeanSide.value φ = B.trace.value φ)
  ∧ (∀ φ : TestPair, B.zeroSide.value φ = B.trace.value φ)
  ∧ (∀ φ : TestPair, B.det2Side.value φ = B.trace.value φ)

theorem certificate_is_admissible (B : ExplicitFormulaBridge) :
    ExplicitFormulaAdmissible B :=
  ⟨B.arith_plus_arch_eq_trace, B.zero_eq_trace, B.det2_eq_trace⟩

/-- Conséquence-pivot : PrimeSide + ArchSide = ZeroSide. -/
theorem prime_plus_arch_eq_spec
    (B : ExplicitFormulaBridge) (φ : TestPair) :
    B.primeSide.value φ + B.archimedeanSide.value φ = B.zeroSide.value φ := by
  rw [B.arith_plus_arch_eq_trace φ, ← B.zero_eq_trace φ]

/-- Conséquence-pivot : PrimeSide + ArchSide = Det2Side. -/
theorem prime_plus_arch_eq_det2
    (B : ExplicitFormulaBridge) (φ : TestPair) :
    B.primeSide.value φ + B.archimedeanSide.value φ = B.det2Side.value φ := by
  rw [B.arith_plus_arch_eq_trace φ, ← B.det2_eq_trace φ]

/-- Conséquence-pivot : ZeroSide = Det2Side. -/
theorem spec_eq_det2
    (B : ExplicitFormulaBridge) (φ : TestPair) :
    B.zeroSide.value φ = B.det2Side.value φ := by
  rw [B.zero_eq_trace φ, ← B.det2_eq_trace φ]

/- ═══════════════════════════════════════════════════════════════════
   GATE FCI — No Certificate ⇒ No Claim
   ═══════════════════════════════════════════════════════════════════ -/

def ExplicitFormulaClaimAllowed (B : ExplicitFormulaBridge) : Prop :=
  ExplicitFormulaAdmissible B

theorem no_explicit_formula_claim_without_certificate
    (B : ExplicitFormulaBridge) (h : ¬ ExplicitFormulaAdmissible B) :
    ¬ ExplicitFormulaClaimAllowed B := h

end CouretUnification.Logic.ExplicitFormula
