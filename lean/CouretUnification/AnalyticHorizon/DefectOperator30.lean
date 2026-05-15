/-
  CouretUnification.AnalyticHorizon.DefectOperator30
  ════════════════════════════════════════════════════════════════════
  Opérateur de défaut sur la structure de Klein ponctuée — couche
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
    • Importe ClosureTC pour Z30, K4.
    • Importe Residue.Bridge.DefectOperatorBridge pour consommer la structure
      ponctuée via un contrat explicite Residue → AnalyticHorizon.
    • Le poids spectral spectralWeight est explicite :
        +1 sur TC,
        -1 sur Phantom19,
         0 ailleurs.

  Doctrine : v38.1 enrichi.
  Statut   : interface matricielle, pas d'instance, 0 sorry.

  Architecture :
    ce fichier ne doit pas importer directement `CouretUnification.Residue.*`,
    sauf via `CouretUnification.Residue.Bridge.*`.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import CouretUnification.Residue.Bridge.DefectOperatorBridge
import CouretUnification.EpistemicDiscipline.BridgeStatus
import CouretUnification.EpistemicDiscipline.DoctrinalInvariants

namespace CouretUnification.AnalyticHorizon

open CouretUnification.Residue.Bridge
open CouretUnification.EpistemicDiscipline   -- ← pour BridgeStatus et RHClaimed

/-! ## §1 — Poids spectral sur la structure de Klein ponctuée -/

/--
Poids spectral de la structure de Klein ponctuée.

  +1 sur TC = {1, 11, 29}
  -1 sur Phantom19 = {19}
   0 ailleurs dans Z30.

La somme signée  Σ w(x) ρ(x)  sur K₄ est l'opérateur de défaut.
-/
def spectralWeight (x : DefectOperatorZ30) : ℤ :=
  if x ∈ defectOperatorTC then 1
  else if x = defectOperatorPhantom19 then -1
  else 0

theorem spectralWeight_one : spectralWeight (1 : DefectOperatorZ30) = 1 := by
  native_decide

theorem spectralWeight_eleven : spectralWeight (11 : DefectOperatorZ30) = 1 := by
  native_decide

theorem spectralWeight_twentynine : spectralWeight (29 : DefectOperatorZ30) = 1 := by
  native_decide

theorem spectralWeight_phantom19 : spectralWeight defectOperatorPhantom19 = -1 := by
  native_decide

/-! ## §2 — Représentation finie abstraite -/

/--
Une représentation finie de Z30 par matrices rationnelles.

Cette représentation est volontairement abstraite : des représentations
concrètes — régulière, décomposée en caractères, de Fourier, de Cayley sur K4,
etc. — pourront être branchées plus tard via des instances de cette structure.

Doctrinalement : le programme ne s'engage PAS sur une représentation unique.
L'opérateur de défaut ci-dessous est paramétré par ρ.
-/
structure FiniteRepresentation
    (ι : Type) [Fintype ι] [DecidableEq ι] where
  rho : DefectOperatorZ30 → Matrix ι ι ℚ

/-! ## §3 — L'opérateur de défaut D_19 -/

/--
L'opérateur de défaut associé à la structure de Klein ponctuée.

  D_19 = Σ_{x ∈ K₄} w(x) · ρ(x)
       = ρ(1) + ρ(11) + ρ(29) − ρ(19)

Cette somme capture le contenu algébrique de « TC corrigé par le fantôme » :
les trois éléments de TC contribuent chacun avec le poids +1, le fantôme
contribue avec le poids −1, et tout le reste de Z30 est invisible.
-/
noncomputable def defectOperator19
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : FiniteRepresentation ι) :
    Matrix ι ι ℚ :=
  ∑ x ∈ defectOperatorK4, (spectralWeight x : ℚ) • ρ.rho x

/-! ## §4 — Cible de trace protégée — interface -/

/--
Une cible de trace protégée sur une représentation finie.

C'est une structure à valeur propositionnelle. Elle ne devient un théorème
qu'une fois que ρ, P_- et A^{nt} sont tous concrets et que la trace est
calculable.

Doctrinalement :
  - P_- est un projecteur SPECTRAL — sur l'espace propre E_{-1}.
  - A^{nt} est un opérateur antisymétrique non tensoriel.
  - La conjecture est Tr(P_- · A^{nt} · P_-) = -12 à q = 30.
-/
structure ProtectedTraceTarget
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (Pminus Ant : Matrix ι ι ℚ) : Prop where
  trace_eq_minus12 :
    Matrix.trace (Pminus * Ant * Pminus) = (-12 : ℚ)

/-- Statut de pont de la cible de trace protégée.

    Actuellement `theoremTarget`, car aucune représentation concrète
    n'a encore été raccordée. -/
def DefectOperator30Status : BridgeStatus :=
  BridgeStatus.theoremTarget

theorem defect_operator_30_status :
    DefectOperator30Status = BridgeStatus.theoremTarget := rfl

/-! ## §5 — Pare-feu doctrinal -/

theorem no_rh_from_defect_operator_30 :
    RHClaimed = false := rfl

end CouretUnification.AnalyticHorizon