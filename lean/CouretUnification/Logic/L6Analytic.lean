/-
# CouretUnification/Logic/L6Analytic.lean

## Rôle
Fournit les DÉFINITIONS EFFECTIVES pour le pont L6, en s'appuyant sur
les fonctions spéciales de Mathlib :

- `Aarch_effective` via `Real.Gamma((1/2+a)/2)` et `log(1+T²)`,
  normalisée par `-(log π)/2` (compensation archimédienne standard).
- `Ztot_effective` via le terme principal de Riemann–von Mangoldt :
  `N(T) ≈ (T/2π) · log(T/(2π·e))`.

## Architecture v35.8.8.1 (refactoring B)
Cette version importe `L6Interface` (types seulement), PAS `L6Bridge`.
Le sens du raccord est maintenant inversé : c'est `L6Bridge` qui
définira `Aarch := Aarch_effective`, ce qui rend les bridges
provables par `rfl`.

## Statut
- Layer     : Logic
- Status    : proved
- Sorry     : 0
- RHClaimed : false
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CouretUnification.Logic.L6Interface
import CouretUnification.Meta.Doctrine

namespace CouretUnification
namespace Logic
namespace L6Analytic

open CouretUnification.Logic.L6Interface
open Real

/-! ## Section 1 — Définitions effectives -/

/-- Contribution archimédienne effective.

    Formule analytique cible :
    ```
    Aarch_effective χ T
      = ( log(Γ((1/2 + a)/2)) + log(1 + T²) ) / 4  -  (log π) / 2
    ```
    où `a = χ.a ∈ {0,1}` est la parité du caractère.

    Le terme `log(Γ((1/2+a)/2))/4` capture la dépendance en parité
    du facteur archimédien.

    Le terme `log(1 + T²)/4` est la queue asymptotique réelle qui se
    substitue, dans cette première itération purement réelle, à
    `Re ψ(1/4 + iT/2)` du Digamma complexe.

    Le terme `-(log π)/2` est la dérivée logarithmique de
    `π^(-(s+a)/2)` dans la fonction complétée
    `ξ(s,χ) = π^(-(s+a)/2) Γ((s+a)/2) L(s,χ)`. Sans ce terme, le ratio
    avec `Ztot_effective` serait décalé d'une constante et ne tendrait
    pas vers `1/2`.

    NB : cette définition est volontairement purement RÉELLE (pas de
    `Complex.Gamma`). Le raffinement en v35.8.7 remplacera la queue
    `log(1 + T²)/4` par la vraie borne Stirling sur `Re ψ`. -/
noncomputable def Aarch_effective (χ : PrimitiveCharacter) (T : ℝ) : ℝ :=
  let a := χ.a
  (Real.log (Real.Gamma ((1/2 + a) / 2)) + Real.log (1 + T^2)) / 4
    - (Real.log Real.pi) / 2

/-- Comptage effectif des zéros : terme principal de Riemann–von Mangoldt.

    Formule analytique :
    ```
    Ztot_effective χ T = (T / 2π) · log( T / (2π · e) )
    ```

    Pour `T > 2π·e ≈ 17.08`, cette fonction est strictement positive
    et croît comme `(T log T)/(2π)`, ce qui domine largement les
    oscillations `O(log T)` du vrai comptage `N(T)`.

    NB : à ce stade la dépendance en `χ` est triviale (le terme principal
    de Riemann–von Mangoldt est le même pour tous les caractères
    primitifs, seul le reste varie). La signature est conservée pour
    permettre un raffinement par conducteur en v36. -/
noncomputable def Ztot_effective (_χ : PrimitiveCharacter) (T : ℝ) : ℝ :=
  let τ := T / (2 * Real.pi)
  τ * Real.log (τ / Real.exp 1)

/-! ## Section 2 — Propriétés analytiques (API pour L6Derived)

    Ces lemmes sont l'API que `L6RatioEstimateDerived.lean` consomme
    pour fermer son Step C. Ils exposent les propriétés asymptotiques
    des définitions effectives sous une forme directement exploitable.

    NB : la section 2 antérieure (théorèmes de raccord `Aarch_bridge` et
    `Ztot_bridge`) a disparu en v35.8.6. Le raccord est désormais réalisé
    dans `L6Bridge.lean` par définition, donc trivialement par `rfl`. -/

/-- Positivité éventuelle du comptage.

    Pour `T > 2π · e`, on a `log(T / (2π·e)) > 0`, donc
    `Ztot_effective χ T > 0`.

    Cette borne numérique (≈ 17.08) est largement suffisante : le
    premier zéro non trivial de ζ se situe à γ₁ ≈ 14.13, donc
    tout `T ≥ 18` garantit simultanément `N(T) ≥ 1` et la positivité
    du terme principal.

    **Fermé en v35.8.8.1** : preuve complète via monotonie stricte de log. -/
theorem Ztot_effective_eventually_positive (χ : PrimitiveCharacter) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T → 0 < Ztot_effective χ T := by
  -- Stratégie : T₀ := 2π·e + 1. Pour T ≥ T₀ :
  --   1) T > 2π·e (car T ≥ 2π·e + 1 > 2π·e)
  --   2) τ := T/(2π) > e > 0
  --   3) τ/e > 1, donc log(τ/e) > 0
  --   4) τ · log(τ/e) > 0.
  refine ⟨2 * Real.pi * Real.exp 1 + 1, ?_, ?_⟩
  · -- 0 < 2π·e + 1
    have h_pi_pos : 0 < Real.pi := Real.pi_pos
    have h_exp_pos : 0 < Real.exp 1 := Real.exp_pos 1
    have h_prod : 0 < 2 * Real.pi * Real.exp 1 := by positivity
    linarith
  · intro T hT
    -- Déplier Ztot_effective : τ = T/(2π), Ztot = τ · log(τ/e)
    show 0 < (T / (2 * Real.pi)) *
            Real.log (T / (2 * Real.pi) / Real.exp 1)
    have h_pi_pos : 0 < Real.pi := Real.pi_pos
    have h_2pi_pos : 0 < 2 * Real.pi := by linarith
    have h_exp_pos : 0 < Real.exp 1 := Real.exp_pos 1
    -- T > 2π·e (strict)
    have h_T_gt : 2 * Real.pi * Real.exp 1 < T := by linarith
    -- τ := T/(2π) satisfait τ > e
    have h_tau_gt_e : Real.exp 1 < T / (2 * Real.pi) := by
      rw [lt_div_iff₀ h_2pi_pos]
      linarith
    -- Donc τ > 0
    have h_tau_pos : 0 < T / (2 * Real.pi) := lt_trans h_exp_pos h_tau_gt_e
    -- τ/e > 1
    have h_tau_div_e_gt_1 : 1 < T / (2 * Real.pi) / Real.exp 1 := by
      rw [lt_div_iff₀ h_exp_pos]
      linarith
    -- log(τ/e) > 0
    have h_log_pos :
        0 < Real.log (T / (2 * Real.pi) / Real.exp 1) :=
      Real.log_pos h_tau_div_e_gt_1
    -- Produit de deux positifs
    exact mul_pos h_tau_pos h_log_pos

/-- Croissance logarithmique de la contribution archimédienne.

    Pour `T` suffisamment grand, `Aarch_effective χ T ≥ (1/8) · log T`.
    Cette borne inférieure est le verrou clé permettant à `L6Derived`
    de dominer les termes d'erreur dans le ratio `eps χ T`.

    Constante `1/8` : vient du terme `log(1 + T²)/4 ~ (log T)/2` pour
    T grand, moins une marge technique pour absorber les constantes
    négligeables `log(Γ(...))/4` et `-(log π)/2`.

    ## Stratégie de preuve complète (prête pour v35.8.7.2)

    Soit `K := log(Γ((1/2+χ.a)/2))/4 - log(π)/2` le terme constant
    dépendant de χ (de signe inconnu, car χ.a est opaque).

    **Choix de témoins** :
    - `C := 1/8`
    - `T₀ := max 2 (exp((8/3) * max 0 (-K))) + 1`

    **Étapes** :

    1. `T ≥ 2` : immédiat par `le_max_left`.
    2. `log T > 0` : `Real.log_pos` avec `T > 1`.
    3. `T ≥ exp((8/3) * max 0 (-K))` : par `le_max_right`.
    4. `log T ≥ (8/3) * max 0 (-K)` :
          via `Real.log_exp` et `Real.log_le_log`.
    5. `log(1 + T²) ≥ 2 log T` pour `T ≥ 1` :
          puisque `T² ≤ 1 + T²`, `Real.log_le_log` donne
          `log T² ≤ log(1+T²)` ; puis `log T² = 2 log T` via
          `Real.log_mul` sur `T · T`.
    6. `-K ≤ max 0 (-K) ≤ (3/8) log T` (par (4)), donc
       `K ≥ -(3/8) log T`.
    7. Aarch_effective χ T = K + log(1+T²)/4
       ≥ -(3/8) log T + (2 log T)/4
       = -(3/8) log T + (log T)/2
       = (1/8) log T ✓

    La preuve formelle fait ~40 lignes. Elle est bornée et ne dépend
    que de noms stables Mathlib (Real.log_pos, Real.log_exp,
    Real.log_le_log, Real.log_mul, Real.exp_pos, ne_of_gt). -/
theorem Aarch_effective_log_growth (χ : PrimitiveCharacter) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 1 < T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → C * Real.log T ≤ Aarch_effective χ T := by
  let K : ℝ :=
    Real.log (Real.Gamma ((1 / 2 + χ.a) / 2)) / 4 - (Real.log Real.pi) / 2
  refine ⟨(1 : ℝ) / 8, by norm_num, max 2 (Real.exp ((8 / 3 : ℝ) * max 0 (-K))), ?_, ?_⟩
  · have htwo : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le htwo (le_max_left _ _)
  · intro T hT
    have hT_ge_two : (2 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
    have hT_gt_one : (1 : ℝ) < T := by linarith
    have hT_pos : (0 : ℝ) < T := by linarith

    have hT_ge_exp : Real.exp ((8 / 3 : ℝ) * max 0 (-K)) ≤ T := by
      exact le_trans (le_max_right _ _) hT

    have hlog_ge :
        (8 / 3 : ℝ) * max 0 (-K) ≤ Real.log T := by
      have hexp_pos : 0 < Real.exp ((8 / 3 : ℝ) * max 0 (-K)) := Real.exp_pos _
      have := Real.log_le_log hexp_pos hT_ge_exp
      simpa [Real.log_exp] using this

    have hmax_le :
        max 0 (-K) ≤ (3 / 8 : ℝ) * Real.log T := by
      linarith

    have hnegK_le : -K ≤ max 0 (-K) := by
      exact le_max_right 0 (-K)

    have hK_bound :
        -(3 / 8 : ℝ) * Real.log T ≤ K := by
      linarith

    have hT2_pos : 0 < T ^ 2 := by positivity
    have hT2_le : T ^ 2 ≤ 1 + T ^ 2 := by linarith

    have hlog_sq_le :
        Real.log (T ^ 2) ≤ Real.log (1 + T ^ 2) := by
      exact Real.log_le_log hT2_pos hT2_le

    have hlog_sq :
        Real.log (T ^ 2) = 2 * Real.log T := by
      have hT_ne : T ≠ 0 := ne_of_gt hT_pos
      calc
        Real.log (T ^ 2) = Real.log (T * T) := by ring_nf
        _ = Real.log T + Real.log T := by rw [Real.log_mul hT_ne hT_ne]
        _ = 2 * Real.log T := by ring

    have harch_part :
        (1 / 2 : ℝ) * Real.log T ≤ Real.log (1 + T ^ 2) / 4 := by
      have : 2 * Real.log T ≤ Real.log (1 + T ^ 2) := by
        simpa [hlog_sq] using hlog_sq_le
      linarith

    have hmain :
        (1 / 8 : ℝ) * Real.log T ≤ K + Real.log (1 + T ^ 2) / 4 := by
      linarith [hK_bound, harch_part]

    have hsplit :
        Aarch_effective χ T = K + Real.log (1 + T ^ 2) / 4 := by
      unfold Aarch_effective
      dsimp [K]
      ring

    rw [hsplit]
    exact hmain

/-! ## Section 3 — Identité doctrinale du fichier -/

open CouretUnification.Meta

/-- Identité doctrinale du fichier L6Analytic (v35.8.8.1).

    Fermetures successives :
      - v35.8.7.1 : `Ztot_effective_eventually_positive`
      - v35.8.8.1 : `Aarch_effective_log_growth`

    Fichier entièrement fermé. -/
def fileIdentity : FileIdentity where
  filename   := "CouretUnification/Logic/L6Analytic.lean"
  layer      := Layer.B
  status     := Status.proved
  sorryCount := 0
  rhClaimed  := false

end L6Analytic
end Logic
end CouretUnification
