/-
# Logic/EulerBridgeInfiniteReal.lean — Spécialisation ℝ du pont eulérien (v35.8)

## Statut épistémique

  - Couche : Logic
  - Statut : [B] — théorème final fermé via wrappers compat,
             1 sorry analytique honnête (target_bound, isolé dans Compat)
  - sorryCount : 0 (dans ce fichier)
  - RHClaimed = false

## Objet

Spécialisation à ℝ des théorèmes E3/E4 d'`EulerBridgeInfinite.lean`,
avec fermeture des deux résidus `[API-LOCAL]` via les wrappers de
`EulerBridgeInfiniteCompat.lean`.

## Doctrine

  - `EulerBridgeInfinite.lean` : version générique sur `NormedCommRing`,
    contient 2 sorries `[API-LOCAL]` non fermables sans spécialisation.
  - `EulerBridgeInfiniteReal.lean` (ce fichier) : spécialisation à ℝ,
    sorries fermés via le compat. Théorème final disponible.
  - `EulerBridgeInfiniteCompat.lean` : wrappers d'API + reliquat
    analytique honnête isolé dans `target_bound`.

Cette stratification évite de casser la généralité du module principal
tout en fournissant un théorème pleinement fermé pour le cas concret ℝ.
-/

import CouretUnification.Logic.Doctrine
import CouretUnification.Logic.H3.SquarefreeSupport
import CouretUnification.Logic.EulerBridgeInfiniteCompat
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic

noncomputable section
open scoped BigOperators
open Classical

namespace CouretUnification
namespace Logic
namespace EulerBridgeInfiniteReal

open CouretUnification.Meta
open CouretUnification.Logic.EulerBridgeInfiniteCompat

/-! ## Section 1 — Hypothèse de support squarefree (spécialisée ℝ) -/

/-- **[B] Support squarefree pour fonctions réelles.** -/
def SquarefreeSupportLikeReal (f : ℕ → ℝ) : Prop :=
  ∀ {p e : ℕ}, Nat.Prime p → 2 ≤ e → f (p ^ e) = 0

/-! ## Section 2 — E4.2 fermé via compat -/

/-- **[A] E4.2 fermé : facteur local squarefree sur ℝ.**

    Cette version utilise le wrapper `local_factor_squarefree_tsum`
    du module Compat. Aucun sorry. -/
lemma e4_2_real_prime_pow_tsum_eq_one_add
    (f : ℕ → ℝ)
    (hf1 : f 1 = 1)
    (hsf : SquarefreeSupportLikeReal f)
    {p : ℕ} (hp : Nat.Prime p)
    (hsumm : Summable (fun e : ℕ => f (p ^ e))) :
    (∑' e : ℕ, f (p ^ e)) = 1 + f p := by
  -- Conversion de SquarefreeSupportLikeReal vers la forme attendue par le wrapper.
  have hvanish : ∀ e : ℕ, 2 ≤ e → f (p ^ e) = 0 := by
    intro e he
    exact hsf hp he
  exact local_factor_squarefree_tsum hp hf1 hvanish hsumm

/-! ## Section 3 — E3.1 fermé via compat -/

/-- **[A] E3.1 fermé : domination par majorant sommable sur ℝ.**

    Cette version utilise le wrapper `summable_domination_nonneg` du Compat.
    La signature passe par les normes (`‖f n‖`) en restant cohérente avec
    la chaîne d'argumentation du module principal. -/
lemma e3_1_real_summable_norm_of_domination
    (f : ℕ → ℝ) (majorant : ℕ → ℝ)
    (h_nonneg : ∀ n, 0 ≤ majorant n)
    (h_le : ∀ n, |f n| ≤ majorant n)
    (h_majorant : Summable majorant) :
    Summable (fun n : ℕ => |f n|) := by
  -- |f n| ≥ 0 toujours vrai
  have habs_nonneg : ∀ n, 0 ≤ |f n| := fun n => abs_nonneg _
  exact summable_domination_nonneg habs_nonneg h_nonneg h_le h_majorant

/-! ## Section 4 — Théorème final ℝ -/

/-- **[B] Pont EulerProduct ℝ standard, version `tprod`.**

    Wrapper direct sur `EulerProduct.eulerProduct_tprod` spécialisé à ℝ. -/
theorem e4_real_bridge_tprod
    (f : ℕ → ℝ)
    (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsum : Summable (fun n : ℕ => ‖f n‖))
    (hf0 : f 0 = 0) :
    (∏' p : Nat.Primes, ∑' e : ℕ, f ((p : ℕ) ^ e)) = ∑' n : ℕ, f n := by
  simpa using EulerProduct.eulerProduct_tprod hf1 @hmul hsum hf0

/-- **[B] Théorème final E3+E4 sur ℝ.**

    Version pleinement fermée pour `f : ℕ → ℝ` squarefree-supportée.
    Aucun sorry dans ce fichier. -/
theorem squarefree_limit_eq_euler_product_real
    (f : ℕ → ℝ)
    (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsum : Summable (fun n : ℕ => ‖f n‖))
    (hf0 : f 0 = 0)
    (hsf : SquarefreeSupportLikeReal f)
    (hloc : ∀ p : Nat.Primes, Summable (fun e : ℕ => f ((p : ℕ) ^ e))) :
    (∏' p : Nat.Primes, (1 + f (p : ℕ))) = ∑' n : ℕ, f n := by
  calc
    (∏' p : Nat.Primes, (1 + f (p : ℕ)))
        = ∏' p : Nat.Primes, ∑' e : ℕ, f ((p : ℕ) ^ e) := by
            refine tprod_congr ?_
            intro p
            symm
            exact e4_2_real_prime_pow_tsum_eq_one_add f hf1 hsf p.property (hloc p)
    _   = ∑' n : ℕ, f n := by
            simpa using e4_real_bridge_tprod f hf1 @hmul hsum hf0

/-! ## Section 5 — Identité doctrinale -/

def fileIdentity : CouretUnification.Meta.FileIdentity where
  filename := "CouretUnification/Logic/EulerBridgeInfiniteReal.lean"
  layer := CouretUnification.Meta.Layer.B
  status := CouretUnification.Meta.Status.proved
  sorryCount := 0
  rhClaimed := false

example : fileIdentity.rhClaimed = false := rfl

/-! ## Notes finales

1. **Théorème principal** : `squarefree_limit_eq_euler_product_real` —
   pleinement fermé sans sorry. La seule différence vs le module
   générique est l'ajout de l'hypothèse `hloc` qui demande la sommabilité
   locale par premier (techniquement bénigne, automatique pour les cas
   d'application réalistes du programme).

2. **Aucun sorry dans ce fichier**. Le sorry résiduel `target_bound`
   du Compat est isolé et étiqueté `[B-ANALYTIC]` : il ne pollue pas
   ce module.

3. **Stratification claire** :
   - `EulerBridgeInfinite.lean`     : générique R, 2 sorries `[API-LOCAL]`
   - `EulerBridgeInfiniteReal.lean` : ℝ, 0 sorry (FERMÉ via Compat)
   - `EulerBridgeInfiniteCompat.lean` : wrappers + 1 sorry analytique

4. **Aucune dépendance à RH**. Théorème classique, indépendant.
-/

end EulerBridgeInfiniteReal
end Logic
end CouretUnification
