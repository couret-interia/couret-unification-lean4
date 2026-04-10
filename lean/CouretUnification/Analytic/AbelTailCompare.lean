import CouretUnification.Analytic.AbelTailCore
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CouretUnification.Analytic.AbelTailCompare

open Real Asymptotics Filter MeasureTheory Set
open CouretUnification.Analytic.AbelTailCore

/-!
# AbelTailCompare

Ce fichier réalise le passage de la domination ponctuelle asymptotique
à une domination intégrale asymptotique sur les queues `Ioi T`.

## Rôle dans l’architecture

`AbelTailCompare` se place au-dessus de `AbelTailCore` :
- `AbelTailCore` contrôle la queue de référence ;
- `AbelTailCompare` transfère ce contrôle à une fonction générale `f`
  vérifiant `f = O(abelIntegrand)`.

## Résultat principal

Sous hypothèses explicites d’intégrabilité sur les queues,
on montre :

`tailIntegral f = O(log T / T^2)`.

## Esprit de preuve

La preuve sépare nettement :
1. l’extraction ponctuelle depuis `IsBigO`,
2. la positivité éventuelle du modèle,
3. la comparaison des intégrales sur `Ioi T`,
4. la transitivité asymptotique finale.

Aucun `sorry`, aucun axiome ajouté.
-/

variable {f : ℝ → ℝ}

/-- Queue intégrale de `f` à partir de `T`.

On intègre `f` sur l’intervalle ouvert à droite `Ioi T = (T, +∞)`. -/
noncomputable def tailIntegral (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ t in Set.Ioi T, f t

/-! ## §1. Extraction ponctuelle depuis `IsBigO` -/

/-- Version directe de l’extraction fournie par `hf.bound`.

Si `f = O(abelIntegrand)` à l’infini, alors il existe une constante `C`
telle que, éventuellement,
`‖f t‖ ≤ C * ‖abelIntegrand t‖`. -/
theorem eventually_abs_le_of_isBigO
    (hf : f =O[atTop] abelIntegrand) :
    ∃ C, ∀ᶠ t in atTop, ‖f t‖ ≤ C * ‖abelIntegrand t‖ :=
  hf.bound

/-! ## §2. Mise sous forme exploitable avec positivité du modèle -/

/-- Extraction ponctuelle sous une forme plus utile pour l’intégration.

À partir de `f = O(abelIntegrand)`, on obtient une constante strictement
positive `C` telle que, pour `t` assez grand,

`‖f t‖ ≤ C * abelIntegrand t`.

La différence avec `eventually_abs_le_of_isBigO` est que l’on remplace
`‖abelIntegrand t‖` par `abelIntegrand t`, ce qui est permis pour `t > 1`
car le modèle est alors non négatif. -/
private lemma eventually_abs_le_model
    (hf : f =O[atTop] abelIntegrand) :
    ∃ C, (0 < C) ∧ ∀ᶠ t in atTop,
      ‖f t‖ ≤ C * abelIntegrand t := by
  rcases hf.bound with ⟨C, hC⟩
  -- On remplace `C` par `max C 1` afin de garantir une constante > 0.
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right C 1), ?_⟩
  filter_upwards [hC, eventually_gt_atTop (1 : ℝ)] with t ht ht1
  have hnonneg : 0 ≤ abelIntegrand t := by
    dsimp [abelIntegrand]
    exact div_nonneg (le_of_lt (Real.log_pos ht1)) (by positivity)
  calc
    ‖f t‖ ≤ C * ‖abelIntegrand t‖ := ht
    _ = C * |abelIntegrand t| := by rw [Real.norm_eq_abs]
    _ = C * abelIntegrand t := by rw [abs_of_nonneg hnonneg]
    _ ≤ max C 1 * abelIntegrand t := by
      apply mul_le_mul_of_nonneg_right (le_max_left C 1) hnonneg

/-! ## §3. Comparaison intégrale abstraite -/

/-- Comparaison intégrale principale.

Si `f = O(abelIntegrand)` et si `f` ainsi que `abelIntegrand` sont
intégrables sur toute queue `Ioi T`, alors la queue intégrale de `f`
est dominée par la queue de référence `abelReferenceTail`.

Autrement dit :

`tailIntegral f = O(abelReferenceTail)` au voisinage de `+∞`.

### Stratégie

- on extrait une domination ponctuelle éventuelle ;
- on la transporte sur toute queue `Ioi T` pour `T` assez grand ;
- on utilise :
  `‖∫ f‖ ≤ ∫ ‖f‖`,
  puis la monotonie de l’intégrale ;
- on conclut par identification avec `abelReferenceTail`. -/
theorem tailIntegral_isBigO_of_isBigO
    (hf : f =O[atTop] abelIntegrand)
    (hf_int : ∀ T, IntegrableOn f (Set.Ioi T))
    (hmod_int : ∀ T, IntegrableOn abelIntegrand (Set.Ioi T)) :
    (fun T => tailIntegral f T) =O[atTop]
      (fun T => abelReferenceTail T) := by
  rcases eventually_abs_le_model hf with ⟨C, hC_pos, hbound⟩
  rcases (eventually_atTop.mp hbound) with ⟨A, hA⟩
  apply IsBigO.of_bound C
  filter_upwards [eventually_gt_atTop (max A 1 : ℝ)] with T hT

  -- À partir de `T > max A 1`, on sait à la fois `A < T` et `1 < T`.
  have hTA : A < T := lt_of_le_of_lt (le_max_left A 1) hT
  have hT1 : 1 < T := lt_of_le_of_lt (le_max_right A 1) hT

  -- Premier verrou : la norme de l’intégrale est majorée par l’intégrale
  -- de la norme.
  have h1 : ‖tailIntegral f T‖ ≤ ∫ t in Set.Ioi T, ‖f t‖ := by
    simpa [tailIntegral] using
      (norm_integral_le_integral_norm
        (f := fun t : ℝ => f t)
        (μ := volume.restrict (Set.Ioi T)))

  -- Deuxième verrou : sur `Ioi T`, la domination ponctuelle vaut partout
  -- puisque `T > A`. On l’intègre ensuite via `integral_mono_ae`.
  have h2 : ∫ t in Set.Ioi T, ‖f t‖ ≤
      C * ∫ t in Set.Ioi T, abelIntegrand t := by
    have hmono : ∀ᵐ t ∂(volume.restrict (Set.Ioi T)),
        ‖f t‖ ≤ C * abelIntegrand t := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall (fun t htT =>
        hA t (le_of_lt (lt_trans hTA htT)))
    calc
      ∫ t in Set.Ioi T, ‖f t‖
          ≤ ∫ t in Set.Ioi T, C * abelIntegrand t :=
            MeasureTheory.integral_mono_ae
              (hf_int T).norm
              ((hmod_int T).const_mul C)
              hmono
      _ = C * ∫ t in Set.Ioi T, abelIntegrand t := by
          simpa using
            (MeasureTheory.integral_const_mul C
              (f := fun t : ℝ => abelIntegrand t)
              (μ := volume.restrict (Set.Ioi T)))

  -- Troisième verrou : la queue de référence est non négative.
  -- Sur `Ioi T`, comme `1 < T`, on a `1 < t`, donc `log t > 0`.
  have href_nonneg : 0 ≤ abelReferenceTail T := by
    dsimp [abelReferenceTail]
    apply MeasureTheory.integral_nonneg_of_ae
    change ∀ᵐ t ∂(volume.restrict (Set.Ioi T)), 0 ≤ abelIntegrand t
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall ?_
    intro t htT
    have ht1' : 1 < t := lt_trans hT1 htT
    dsimp [abelIntegrand]
    exact div_nonneg (le_of_lt (Real.log_pos ht1')) (by positivity)

  -- Assemblage final :
  -- `‖tailIntegral f T‖ ≤ C * abelReferenceTail T = C * ‖abelReferenceTail T‖`.
  calc
    ‖tailIntegral f T‖ ≤ C * ∫ t in Set.Ioi T, abelIntegrand t := by
      linarith [h1, h2]
    _ = C * abelReferenceTail T := by rfl
    _ = C * ‖abelReferenceTail T‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg href_nonneg]

/-! ## §4. Théorème final -/

/-- Estimation asymptotique finale des queues.

Si `f` est asymptotiquement dominée par `abelIntegrand`, alors
sa queue intégrale vérifie :

`tailIntegral f = O(log T / T^2)`.

La preuve est une simple composition :

1. `tailIntegral f = O(abelReferenceTail)` par comparaison abstraite ;
2. `abelReferenceTail = O(log T / T^2)` par le résultat du fichier cœur. -/
theorem abelTailEstimate
    (hf : f =O[atTop] abelIntegrand)
    (hf_int : ∀ T, IntegrableOn f (Set.Ioi T))
    (hmod_int : ∀ T, IntegrableOn abelIntegrand (Set.Ioi T))
    (hderiv_global : ∀ x > 0,
      HasDerivAt abelPrimitive (abelIntegrand x) x) :
    (fun T => tailIntegral f T) =O[atTop]
      (fun T => Real.log T / T ^ 2) :=
  (tailIntegral_isBigO_of_isBigO hf hf_int hmod_int).trans
    (abelReferenceTail_isBigO hderiv_global)

/-- Audit local : aucun `sorry` dans ce fichier. -/
def sorryCount : Nat := 0

/-- Audit local : aucun axiome ajouté dans ce fichier. -/
def axiomCount : Nat := 0

end CouretUnification.Analytic.AbelTailCompare
