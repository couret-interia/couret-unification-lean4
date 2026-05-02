/-
  CouretUnification.AnalyticHorizon.DefectOperator30
  ════════════════════════════════════════════════════════════════════
  Opérateur de défaut sur la structure Klein ponctué — couche
  matricielle, complément de `ProtectedMinusTraceTargets.lean`.

  Là où `ProtectedMinusTraceTargets` POSE la valeur scalaire -12 comme
  définition, ce module fournit la CONSTRUCTION matricielle abstraite
  qui produira cette valeur, une fois une représentation concrète
  fournie. Les deux modules ne se substituent pas l'un à l'autre :
    • ProtectedMinusTraceTargets : invariant scalaire -12 (hypothèse).
    • DefectOperator30           : structure matricielle qui le porte.

  Les valeurs spécifiques (P_-, A^{nt}, ρ) restent NON CONSTRUITES :
  ce module définit l'interface mais n'instancie aucune représentation.

  REFACTOR v38.1 :
    • Importe ClosureTC pour Z30, K4
    • Importe PuncturedKlein30 pour la structure ponctuée
    • Le poids spectral spectralWeight est explicite (+1 sur TC, -1
      sur Phantom19, 0 ailleurs)

  Doctrine : v38.1 enrichi
  Status   : interface matricielle, pas d'instance, 0 sorry.
-/

import Mathlib
import CouretUnification.Residue.PuncturedKlein30

namespace CouretUnification
namespace AnalyticHorizon

open CouretUnification.Residue

/-! ## §1 — Spectral weight on the punctured Klein structure -/

/--
Spectral weight of the punctured Klein structure.

  +1 on TC = {1, 11, 29}
  -1 on Phantom19 = {19}
   0 elsewhere in Z30.

The signed sum  Σ w(x) ρ(x)  over K₄ is the defect operator.
-/
def spectralWeight (x : Z30) : ℤ :=
  if x ∈ TC then 1
  else if x = Phantom19 then -1
  else 0

theorem spectralWeight_one : spectralWeight (1 : Z30) = 1 := by
  unfold spectralWeight
  have h : (1 : Z30) ∈ TC := by native_decide
  simp [h]

theorem spectralWeight_eleven : spectralWeight (11 : Z30) = 1 := by
  unfold spectralWeight
  have h : (11 : Z30) ∈ TC := by native_decide
  simp [h]

theorem spectralWeight_twentynine : spectralWeight (29 : Z30) = 1 := by
  unfold spectralWeight
  have h : (29 : Z30) ∈ TC := by native_decide
  simp [h]

theorem spectralWeight_phantom19 : spectralWeight Phantom19 = -1 := by
  unfold spectralWeight Phantom19
  have h1 : (19 : Z30) ∉ TC := by native_decide
  have h2 : (19 : Z30) = Phantom19 := rfl
  simp [h1, h2]

/-! ## §2 — Abstract finite representation -/

/--
A finite representation of Z30 by rational matrices.

This is deliberately abstract: concrete representations (regular,
character-decomposed, Fourier, Cayley-of-K4, ...) can be plugged in
later through instances of this structure.

Doctrinally: the program does NOT commit to a single representation.
The defect operator below is parametrised by ρ.
-/
structure FiniteRepresentation
    (ι : Type) [Fintype ι] [DecidableEq ι] where
  rho : Z30 → Matrix ι ι ℚ

/-! ## §3 — The defect operator D_19 -/

/--
The defect operator associated with the punctured Klein structure.

  D_19 = Σ_{x ∈ K₄} w(x) · ρ(x)
       = ρ(1) + ρ(11) + ρ(29) − ρ(19)

This sum captures the algebraic content of "TC corrected by the
phantom" : the three TC elements contribute +1 each, the phantom
contributes −1, and everything else in Z30 is invisible.
-/
noncomputable def defectOperator19
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : FiniteRepresentation ι) :
    Matrix ι ι ℚ :=
  ∑ x ∈ K4, (spectralWeight x : ℚ) • ρ.rho x

/-! ## §4 — Protected trace target (interface) -/

/--
A protected trace target on a finite representation.

This is a Prop-valued structure. It becomes a theorem only once
ρ, P_-, and A^{nt} are all concrete and the trace is computable.

Doctrinally:
  - P_- is a SPECTRAL projector (onto the eigenspace E_{-1})
  - A^{nt} is a non-tensor anti-symmetric operator
  - The conjecture is Tr(P_- · A^{nt} · P_-) = -12 at q=30.
-/
structure ProtectedTraceTarget
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Pminus Ant : Matrix ι ι ℚ) : Prop where
  trace_eq_minus12 :
    Matrix.trace (Pminus * Ant * Pminus) = (-12 : ℚ)

/-- Bridge status of the protected trace target.
    Currently `theoremTarget` because no concrete representation
    has been wired in. -/
def DefectOperator30Status : BridgeStatus :=
  BridgeStatus.theoremTarget

theorem defect_operator_30_status :
    DefectOperator30Status = BridgeStatus.theoremTarget := rfl

/-! ## §5 — Doctrinal firewall -/

theorem no_rh_from_defect_operator_30 :
    RHClaimed = false := rfl

end AnalyticHorizon
end CouretUnification
