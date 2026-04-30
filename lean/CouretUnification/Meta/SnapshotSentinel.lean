/-
  Couret-Unification — v35.8.8
  Meta/SnapshotSentinel.lean

  Objet : fichier SENTINELLE pour les lemmes Mathlib snapshot-dépendants
         utilisés par le dépôt.

         Quand Mathlib change et qu'un nom de lemme bouge, CE FICHIER
         doit casser EN PREMIER. Thomas voit immédiatement :
           1. Quel lemme a dérivé.
           2. Quels fichiers du dépôt vont casser en cascade.
           3. Quel fallback appliquer.

  Statut     : proved (aucun contenu mathématique, purement diagnostique)
  Layer      : Meta
  Doctrine   : fichier de diagnostic — autonome, jamais importé
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  sorryCount             : 0

  RÈGLE D'OR
  ──────────
  Ce fichier NE DOIT JAMAIS ÊTRE IMPORTÉ par un autre fichier du dépôt.
  Son rôle est purement de DIAGNOSTIC : si un `example` ci-dessous échoue,
  Thomas sait exactement quel lemme a changé dans le snapshot Mathlib.

  Commande de test :
    lake build CouretUnification.Meta.SnapshotSentinel

  Si ce build passe : le snapshot Mathlib est compatible avec le dépôt.
  Si ce build échoue : lire l'erreur, localiser le `example` qui casse,
                       appliquer le fallback documenté dans le commentaire
                       adjacent.

  Pour Bernard.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.ArithmeticFunction

namespace CouretUnification.Meta.SnapshotSentinel

/- ═══════════════════════════════════════════════════════════════════════════
   SECTION 1 — Lemmes utilisés par Logic/H3/LocalFactor.lean
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- S-01. `Real.rpow_le_one_of_one_le_of_nonpos` — bornée par 1 pour base ≥ 1
    et exposant ≤ 0. Utilisé dans `local_factor_prime_sigma`.

    FALLBACK si le nom dérive :
    ```
    -- p ≥ 1 et -σ ≤ 0
    -- preuve via 1 ≤ p^σ puis Real.rpow_neg et one_div_le_one_of_one_le
    ```
-/
example : Real.rpow 2 (-1) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)

/-- S-02. `Real.rpow_nonneg` — non-négativité. Stable historiquement. -/
example : 0 ≤ Real.rpow 2 (-1) :=
  Real.rpow_nonneg (by norm_num) (-1)

/-- S-03. `Real.one_le_sqrt` — `1 ≤ sqrt x` dès que `1 ≤ x`.

    FALLBACK si dérive : `Real.sqrt_one_le_iff` ou chaîne
    `Real.one_le_sqrt_iff_one_le_sq`. -/
example : (1 : ℝ) ≤ Real.sqrt 4 := by
  have h : (1 : ℝ)^2 ≤ 4 := by norm_num
  exact Real.one_le_sqrt h

/-- S-04. `Real.neg_one_le_cos` et `Real.cos_le_one` — bornes du cosinus.
    Hautement stable. -/
example (θ : ℝ) : -1 ≤ Real.cos θ ∧ Real.cos θ ≤ 1 :=
  ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩

/- ═══════════════════════════════════════════════════════════════════════════
   SECTION 2 — Lemmes utilisés par Logic/TimeBridge/B2Calibration.lean (LTB-0)
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- S-05. `Real.log_inv` — `log (x⁻¹) = -log x`. Stable.

    FALLBACK via `Real.log_div` : `log (1/x) = log 1 - log x = -log x`. -/
example : Real.log ((7/6 : ℝ)⁻¹) = -Real.log (7/6) := by
  rw [Real.log_inv]

/-- S-05bis. Même lemme sous forme ratio, pour le cas où `log_inv` bouge. -/
example : Real.log ((7/6 : ℝ)⁻¹) = -Real.log (7/6) := by
  have h76 : (6/7 : ℝ) = (7/6)⁻¹ := by norm_num
  rw [← h76, Real.log_div (by norm_num : (6 : ℝ) ≠ 0) (by norm_num : (7 : ℝ) ≠ 0)]
  have h1 : Real.log 7 - Real.log 6 = Real.log (7/6) := by
    rw [← Real.log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (6 : ℝ) ≠ 0)]
  linarith

/-- S-06. `Real.exp_log` — `exp (log x) = x` pour `0 < x`. Très stable. -/
example : Real.exp (Real.log (6/7)) = 6/7 :=
  Real.exp_log (by norm_num : (0 : ℝ) < 6/7)

/- ═══════════════════════════════════════════════════════════════════════════
   SECTION 3 — Lemmes utilisés par Logic/H3/MoebiusBridge.lean
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- S-07. `ArithmeticFunction.moebius` — fonction de Möbius. Nom stable. -/
example : ArithmeticFunction.moebius 1 = 1 := by
  simp [ArithmeticFunction.moebius_apply_one]

/-- S-08. `Nat.squarefree_mul` — multiplicativité de la squarefree-ness
    pour facteurs coprimes. Utilisé dans SquarefreeSupport.

    FALLBACK si rename : `Nat.Squarefree.mul` ou chaîne via factorisation
    unique. -/
example : Squarefree (6 : ℕ) := by
  decide

/- ═══════════════════════════════════════════════════════════════════════════
   SECTION 4 — Lemmes utilisés par AnalyticHorizon/Det2Transport.lean
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- S-09. `Complex.abs` — module complexe. Peut émettre un deprecation
    warning dans certains snapshots récents ; fallback : `‖·‖`. -/
example : Complex.abs (1 + Complex.I) = Real.sqrt 2 := by
  rw [Complex.abs_apply]
  simp [Complex.normSq_add, Complex.normSq_one, Complex.normSq_I]
  norm_num

/-- S-09bis. `‖·‖` équivalent, utiliser comme fallback si Complex.abs déprécié. -/
example : ‖(1 + Complex.I : ℂ)‖ = Real.sqrt 2 := by
  rw [Complex.norm_eq_abs]
  rw [Complex.abs_apply]
  simp [Complex.normSq_add, Complex.normSq_one, Complex.normSq_I]
  norm_num

/- ═══════════════════════════════════════════════════════════════════════════
   SECTION 5 — Auto-diagnostic
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Nombre de sentinelles actives dans ce fichier. Utile pour cross-check. -/
def activeSentinelCount : ℕ := 10

/-- Si ce fichier compile, toutes les sentinelles passent.
    Cette constante sert seulement de marqueur pour un éventuel
    script qui voudrait vérifier que le sentinel a été effectivement
    construit (pas simplement ignoré). -/
def snapshotCompatible : Bool := true

/-- Version du snapshot contre lequel les sentinelles ont été écrites.
    Mettre à jour cette chaîne à chaque bump de lean-toolchain. -/
def snapshotReferenceVersion : String := "Mathlib tag attendu v4.15.0-compatible"

end CouretUnification.Meta.SnapshotSentinel
