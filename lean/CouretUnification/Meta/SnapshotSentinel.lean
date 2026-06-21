/-
  Couret-Unification — v35.8.10
  Meta/SnapshotSentinel.lean

  Objet : fichier SENTINELLE pour les lemmes Mathlib snapshot-dépendants
          utilisés par le dépôt.

  Philosophie de robustesse
  ─────────────────────────
  Pour chaque dépendance externe importante, on distingue :

    (A) sentinelle de NOM   : `#check Foo.bar`
        -> casse exactement si le nom disparaît / est renommé.

    (B) sentinelle de FORME : `example : ... := by ...`
        -> casse si l’énoncé utile ou son orientation dérive.

  Règles éditoriales
  ──────────────────
  1. Une sentinelle = un seul lemme externe.
  2. Pas de conjonction artificielle liant deux lemmes différents.
  3. Pas de `simp [nom]` quand `exact` / `simpa using` suffit.
  4. Pas de test de décidabilité quand on veut tester un vrai lemme.
  5. Importer directement le fichier du lemme critique quand c’est raisonnable.
  6. Les fallbacks restent dans les commentaires, pas comme sentinelles actives.

  Doctrine   : diagnostic pur — autonome, jamais importé
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  sorryCount             : 0

  Commande :
    lake build CouretUnification.Meta.SnapshotSentinel
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

namespace CouretUnification.Meta.SnapshotSentinel

/- ═══════════════════════════════════════════════════════════════════════════
   SECTION 1 — Logic/H3/LocalFactor.lean
   ═══════════════════════════════════════════════════════════════════════════ -/

/- S-01 NOM — borne supérieure pour `rpow` avec base ≥ 1 et exposant ≤ 0. -/
#check Real.rpow_le_one_of_one_le_of_nonpos

/-- S-01 FORME. -/
example : Real.rpow 2 (-1) ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)

/- S-02 NOM — non-négativité de `rpow`. -/
#check Real.rpow_nonneg

/-- S-02 FORME. -/
example : 0 ≤ Real.rpow 2 (-1) := by
  exact Real.rpow_nonneg (by norm_num) (-1)

/- S-03 NOM — en snapshot actuel, `Real.one_le_sqrt` est un `↔`. -/
#check Real.one_le_sqrt

/-- S-03 FORME.
    Ici on force explicitement l’usage de la direction `.2` du `↔`.
-/
example : (1 : ℝ) ≤ Real.sqrt 4 := by
  exact (Real.one_le_sqrt).2 (by norm_num)

/- S-04a NOM — borne inférieure du cosinus. -/
#check Real.neg_one_le_cos

/-- S-04a FORME. -/
example (θ : ℝ) : -1 ≤ Real.cos θ := by
  exact Real.neg_one_le_cos θ

/- S-04b NOM — borne supérieure du cosinus. -/
#check Real.cos_le_one

/-- S-04b FORME. -/
example (θ : ℝ) : Real.cos θ ≤ 1 := by
  exact Real.cos_le_one θ

/- ═══════════════════════════════════════════════════════════════════════════
   SECTION 2 — Logic/TimeBridge/B2Calibration.lean
   ═══════════════════════════════════════════════════════════════════════════ -/

/- S-05 NOM — logarithme de l’inverse. -/
#check Real.log_inv

/-- S-05 FORME.
    Version plus stricte que `rw [Real.log_inv]` : on force la
    forme exacte du lemme instancié.
    FALLBACK si rename :
      preuve via `Real.log_div` et `log 1 = 0`.
-/
example : Real.log ((7 / 6 : ℝ)⁻¹) = -Real.log (7 / 6) := by
  simpa using (Real.log_inv (7 / 6 : ℝ))

/- S-06 NOM — `exp (log x) = x` pour `0 < x`. -/
#check Real.exp_log

/-- S-06 FORME. -/
example : Real.exp (Real.log (6 / 7)) = 6 / 7 := by
  exact Real.exp_log (by norm_num : (0 : ℝ) < 6 / 7)

/- ═══════════════════════════════════════════════════════════════════════════
   SECTION 3 — Logic/H3/MoebiusBridge.lean
   ═══════════════════════════════════════════════════════════════════════════ -/

/- S-07 NOM — valeur de Möbius en 1. -/
#check ArithmeticFunction.moebius_apply_one

/-- S-07 FORME. -/
example : ArithmeticFunction.moebius 1 = 1 := by
  exact ArithmeticFunction.moebius_apply_one

/- S-08 NOM — multiplicativité squarefree sur ℕ sous coprimalité. -/
#check Nat.squarefree_mul

/-- S-08 FORME.
    On teste le vrai lemme ciblé, pas une décidabilité annexe.
-/
example : Squarefree ((2 : ℕ) * 3) ↔ Squarefree 2 ∧ Squarefree 3 := by
  simpa using
    (Nat.squarefree_mul (m := 2) (n := 3) (show (2 : ℕ).Coprime 3 by decide))

/- ═══════════════════════════════════════════════════════════════════════════
   SECTION 4 — AnalyticHorizon/Det2Transport.lean
   ═══════════════════════════════════════════════════════════════════════════ -/

/- S-09 NOM — formule robuste de norme complexe. -/
#check Complex.norm_add_mul_I

/-- S-09 FORME.
    On reste volontairement sur la norme, pas sur `Complex.abs`.
-/
example : ‖((1 : ℂ) + Complex.I)‖ = Real.sqrt 2 := by
  have h := Complex.norm_add_mul_I (1 : ℝ) 1
  norm_num at h
  simpa [one_mul] using h

/- ═══════════════════════════════════════════════════════════════════════════
   SECTION 5 — Auto-diagnostic
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- 9 sentinelles de NOM + 9 sentinelles de FORME. -/
def activeSentinelCount : ℕ := 18

/-- Marqueur booléen minimal pour scripts externes. -/
def snapshotCompatible : Bool := true

/-- Version déclarative locale. -/
def snapshotReferenceVersion : String := "Lean 4.29.1 / Mathlib snapshot local"

end CouretUnification.Meta.SnapshotSentinel
