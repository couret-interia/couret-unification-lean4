/-
  Couret-Unification — v35.9.0
  Logic/ExplicitFormula/ExplicitFormulaBridge.lean

  Objet : LE MIROIR ARITHMÉTICO-SPECTRAL.

  Statut     : Frozen-eligible (0 sorry, 0 axiome local, structures + théorèmes triviaux)
  Layer      : Logic.ExplicitFormula
  Doctrine   : NO RH HYPOTHESIS allowed in this file.
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0
  axiomCount             : 0

  Voûte commutative cible :

      PrimeSide(f) + ArchimedeanSide(f) = TraceObject(f)
      ZeroSide(f)                       = TraceObject(f)
      Det2Side(f)                       = TraceObject(f)

  Changement v35.9-pre → v35.9.0 :
    • Float → ℂ via Mathlib.

  Pour Bernard.
-/

import Mathlib.Data.Complex.Basic
import CouretUnification.Logic.ExplicitFormula.TestFunctions

namespace CouretUnification.Logic.ExplicitFormula

/- ═══════════════════════════════════════════════════════════════════════════
   LES QUATRE SIDES + L'OBJET TRACE
   ═══════════════════════════════════════════════════════════════════════════ -/

structure TraceObject where
  value : TestPairAdmissible → ℂ

structure PrimeSideOfBridge where
  value : TestPairAdmissible → ℂ

structure ZeroSide where
  value : TestPairAdmissible → ℂ

structure ArchimedeanSide where
  value : TestPairAdmissible → ℂ

structure Det2Side where
  value : TestPairAdmissible → ℂ

/- ═══════════════════════════════════════════════════════════════════════════
   LE CERTIFICAT DE MIROIR (4 SIDES = 1 TRACE)
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Le certificat de la formule explicite, pierre angulaire du programme. -/
structure ExplicitFormulaCertificate where
  traceSide        : TraceObject
  primeSide        : PrimeSideOfBridge
  zeroSide         : ZeroSide
  archimedeanSide  : ArchimedeanSide
  det2Side         : Det2Side
  /-- Égalité 1 : prime + arch = trace (forme canonique de Weil). -/
  arith_plus_arch_eq_trace :
    ∀ φ : TestPairAdmissible, Admissible φ →
      primeSide.value φ + archimedeanSide.value φ = traceSide.value φ
  /-- Égalité 2 : la somme spectrale = la trace. -/
  spec_eq_trace :
    ∀ φ : TestPairAdmissible, Admissible φ →
      zeroSide.value φ = traceSide.value φ
  /-- Égalité 3 : la lecture déterminantielle = la trace. -/
  det2_eq_trace :
    ∀ φ : TestPairAdmissible, Admissible φ →
      det2Side.value φ = traceSide.value φ

def ExplicitFormulaAdmissible (c : ExplicitFormulaCertificate) : Prop :=
  (∀ φ : TestPairAdmissible, Admissible φ →
      c.primeSide.value φ + c.archimedeanSide.value φ = c.traceSide.value φ)
  ∧ (∀ φ : TestPairAdmissible, Admissible φ →
      c.zeroSide.value φ = c.traceSide.value φ)
  ∧ (∀ φ : TestPairAdmissible, Admissible φ →
      c.det2Side.value φ = c.traceSide.value φ)

theorem certificate_is_admissible (c : ExplicitFormulaCertificate) :
    ExplicitFormulaAdmissible c :=
  ⟨c.arith_plus_arch_eq_trace, c.spec_eq_trace, c.det2_eq_trace⟩

/-- Conséquence-pivot : prime + arch = zero. -/
theorem prime_plus_arch_eq_spec
    (c : ExplicitFormulaCertificate)
    (φ : TestPairAdmissible) (h : Admissible φ) :
    c.primeSide.value φ + c.archimedeanSide.value φ = c.zeroSide.value φ := by
  rw [c.arith_plus_arch_eq_trace φ h, ← c.spec_eq_trace φ h]

/-- Conséquence-pivot : prime + arch = det2. -/
theorem prime_plus_arch_eq_det2
    (c : ExplicitFormulaCertificate)
    (φ : TestPairAdmissible) (h : Admissible φ) :
    c.primeSide.value φ + c.archimedeanSide.value φ = c.det2Side.value φ := by
  rw [c.arith_plus_arch_eq_trace φ h, ← c.det2_eq_trace φ h]

/-- Conséquence-pivot : zero = det2. -/
theorem spec_eq_det2
    (c : ExplicitFormulaCertificate)
    (φ : TestPairAdmissible) (h : Admissible φ) :
    c.zeroSide.value φ = c.det2Side.value φ := by
  rw [c.spec_eq_trace φ h, ← c.det2_eq_trace φ h]

/- ═══════════════════════════════════════════════════════════════════════════
   GATE FCI : NO CERTIFICATE ⇒ NO CLAIM
   ═══════════════════════════════════════════════════════════════════════════ -/

def ExplicitFormulaClaimAllowed (c : ExplicitFormulaCertificate) : Prop :=
  ExplicitFormulaAdmissible c

theorem no_explicit_formula_claim_without_certificate
    (c : ExplicitFormulaCertificate)
    (h : ¬ ExplicitFormulaAdmissible c) :
    ¬ ExplicitFormulaClaimAllowed c := h

end CouretUnification.Logic.ExplicitFormula
