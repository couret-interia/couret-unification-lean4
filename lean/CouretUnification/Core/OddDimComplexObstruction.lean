import Mathlib.Tactic
-- import CouretUnification.Core.U30
import CouretUnification.Core.SymplecticObstruction

open CouretUnification.Core.SymplecticObstruction

namespace CouretUnification.Core.OddDimComplexObstruction

/-!
# Obstruction en dimension impaire : J² = −I impossible sur ℤ (ou ℝ)

Pour qu'un espace réel (ou entier) de dimension n admette une structure
complexe linéaire J avec J² = −I, il faut n pair.

**Argument déterminantal** :
  det(J²) = det(J)² ≥ 0
  det(−I) = (−1)ⁿ
  Si n impair : (−1)ⁿ = −1 < 0, contradiction.

Ce fichier formalise le **noyau scalaire** de cet argument :
  ¬ ∃ d : ℤ, d² = (−1)ⁿ  pour n impair.

Le passage complet J² = −I ⟹ det(J)² = (−1)ⁿ nécessiterait
`Matrix.det_mul` et `Matrix.det_neg` de Mathlib, non invoqués ici.

**Validité** : sur tout anneau ordonné (ℤ, ℝ, corps réel clos).
Contre-exemple sur F₂ : en dimension 1, J = [1] donne J² = I = −I.

Appliqué aux sous-ensembles impairs de (ℤ/30ℤ)× :
  |TC| = 3, |V₅| = 5 ⟹ pas de structure complexe réelle.
-/

-- ═══════════════════════════════════════════
-- Noyau scalaire de l’obstruction
-- ═══════════════════════════════════════════

/-- Forme générale : toute dimension impaire crée une obstruction. -/
theorem odd_dim_obstructs (n : Nat) (hn : ∃ k, n = 2 * k + 1) :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ n := by
  obtain ⟨k, rfl⟩ := hn
  exact no_square_root_neg_one_odd k

-- ═══════════════════════════════════════════
-- Application : sous-ensembles de (ℤ/30ℤ)× (alias)
-- ═══════════════════════════════════════════

/-- Obstruction déterminantale en dimension 5 (V₅). Alias de `no_symplectic_dim5`. -/
theorem obstruction_dim5 :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ 5 := no_symplectic_dim5

/-- Obstruction déterminantale en dimension 3 (TC). Alias de `no_symplectic_TC`. -/
theorem obstruction_dim3 :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ 3 := no_symplectic_TC

/-- Obstruction déterminantale en dimension 1. Alias de `no_symplectic_dim1`. -/
theorem obstruction_dim1 :
    ¬ ∃ d : Int, d * d = (-1 : Int) ^ 1 := no_symplectic_dim1

/-!
## Synthèse

**Ce que ce fichier prouve (noyau scalaire) :**
  ¬ ∃ d : ℤ, d² = (−1)ⁿ  pour tout n impair.

**Ce que cela implique (informellement, via det(J²) = det(J)² et det(−I) = (−1)ⁿ) :**
  Aucune matrice réelle ou entière J de taille impaire ne satisfait J² = −I.

**Ce que ce fichier ne formalise PAS :**
  Le passage matriciel det(J²) = det(J)², qui nécessiterait
  `Matrix.det_mul` depuis Mathlib.

**Portée :** valable sur ℤ, ℝ, et tout anneau ordonné où les carrés sont ≥ 0.
Non valable sur F₂ ni sur ℂ.

**Application :** les sous-ensembles de cardinal impair de (ℤ/30ℤ)× — notamment
TC (|TC|=3) et V₅ (|V₅|=5) — ne peuvent pas porter une structure complexe réelle
J² = −I.
-/

end CouretUnification.Core.OddDimComplexObstruction
