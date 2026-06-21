/-
  CouretUnification.Logic.ExplicitFormula.PrimeSideCompactSupport
  ════════════════════════════════════════════════════════════════════
  Fonction test log-compacte pour le côté premier de la formule explicite.

  Ce fichier fournit une version sûre pour la couche Frozen du support compact :
  au lieu de manipuler directement un support analytique général, on impose
  une coupure entière `cutoff` telle que, au-delà de cette coupure, les deux
  valeurs logarithmiques

      g(log n)      et      g(-log n)

  s'annulent.

  Rôle :
    • typer une classe de fonctions test adaptées au côté arithmétique ;
    • montrer que les termes côté premier deviennent nuls après la coupure ;
    • éviter toute sommation infinie effective dans cette couche ;
    • réutiliser `ArithmeticWeight` depuis son fichier canonique.

  Déduplication v38 :
    `ArithmeticWeight` vit désormais dans
    `CouretUnification.Logic.ExplicitFormula.ArithmeticWeight`.
    Ce fichier ne le redéfinit pas.

  Garde-fous :
    • aucune formule explicite globale n'est prouvée ici ;
    • aucune convergence analytique n'est revendiquée ;
    • aucune conséquence RH n'est exportée ;
    • ce fichier ferme seulement l'annulation éventuelle des termes
      arithmétiques sous hypothèse de log-compacité.

  Statut :
    interface logique finie / Frozen-safe ;
    preuve locale sans `sorry`.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CouretUnification.Logic.ExplicitFormula.TraceObject
import CouretUnification.Logic.ExplicitFormula.ArithmeticWeight

namespace CouretUnification.Logic.ExplicitFormula

-- `ArithmeticWeight` vit désormais dans `ArithmeticWeight.lean` — source canonique.
-- v38 : déduplication post-Frozen v36.0.

-- Lignes supprimées : `ArithmeticWeight` vient maintenant de l'import ci-dessus,
-- dans sa version canonique avec `weight : ℕ → ℝ`.

/--
Une fonction test log-compacte.

C'est la version sûre pour la couche Frozen du support compact :
à partir d'une certaine coupure entière, `g(log n)` et `g(-log n)`
s'annulent tous deux.
-/
structure LogCompactTest where
  g : ℝ → ℂ
  cutoff : ℕ
  vanishes_after_cutoff :
    ∀ n : ℕ, cutoff < n →
      g (Real.log n) = 0 ∧ g (-Real.log n) = 0

/-- Terme abstrait du côté premier. -/
noncomputable def primeTermLogCompact
    (Λ : ArithmeticWeight) (φ : LogCompactTest) (n : ℕ) : ℂ :=
  (Λ.weight n : ℂ) * (φ.g (Real.log n) + φ.g (-Real.log n))

/--
Fermeture Frozen du côté premier :
après la coupure, chaque terme du côté premier est nul.
-/
theorem primeTermLogCompact_eventually_zero
    (Λ : ArithmeticWeight)
    (φ : LogCompactTest) :
    ∀ n : ℕ, φ.cutoff < n → primeTermLogCompact Λ φ n = 0 := by
  intro n hn
  unfold primeTermLogCompact
  have hvanish := φ.vanishes_after_cutoff n hn
  rw [hvanish.1, hvanish.2]
  simp

end CouretUnification.Logic.ExplicitFormula
