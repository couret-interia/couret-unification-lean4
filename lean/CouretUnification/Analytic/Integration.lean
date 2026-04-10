import CouretUnification.Analytic.AbelTailCompare
import CouretUnification.Analytic.ZeroDensityAxioms

namespace CouretUnification.Analytic.Integration

open Real Asymptotics Filter MeasureTheory Set
open CouretUnification.Analytic.AbelTailCore
open CouretUnification.Analytic.AbelTailCompare
open CouretUnification.Analytic.ZeroDensityAxioms

/-!
# `Integration.lean` — Greffe T5 vers le pipeline spectral

Ce fichier réalise une étape de **greffe analytique** :
à partir des hypothèses abstraites de type Abel/T5, on construit
un objet `SpectralData` directement exploitable par le pipeline spectral.

## Idée mathématique

On part de trois fonctions réelles :

- `N` : terme de comptage / densité cumulée,
- `w` : poids spectral,
- `wDeriv` : dérivée du poids.

On suppose :

- une borne de type densité de zéros sur `N`,
- une décroissance suffisante de `w`,
- une décroissance suffisante de `wDeriv`,
- une comparaison asymptotique entre l’intégrande réel `N * wDeriv`
  et l’intégrande modèle `abelIntegrand`,
- l’intégrabilité sur toute queue `(T, +∞)`,
- et enfin la dérivabilité globale de la primitive modèle `abelPrimitive`.

Sous ces hypothèses, le théorème `abelTailEstimate` fournit le contrôle
asymptotique de la queue intégrale, ce qui permet d’assembler un
`SpectralData`.

## Remarque de calculabilité

La définition est `noncomputable` car le champ `residualTail` repose sur
`tailIntegral`, qui lui-même est non calculable dans Lean
(théorie de l’intégration classique).
-/

/--
Construit une donnée spectrale `SpectralData` à partir du paquet
d’hypothèses Abel/T5.

Cette définition sert de **pont** entre :

- le bloc analytique de comparaison de queue (`AbelTailCompare`),
- et le bloc de données spectral utilisé plus haut dans le projet.

### Lecture des hypothèses

- `hZeroDensity` : contrôle de croissance de `N(T)` ;
- `hWeightDecay` : décroissance du poids `w(T)` ;
- `hWeightDerivDecay` : décroissance de `w'(T)` ;
- `hIntegrand` : comparaison asymptotique de l’intégrande réel
  avec l’intégrande modèle ;
- `hIntegrandInt` : intégrabilité de l’intégrande réel sur chaque queue ;
- `hModelInt` : intégrabilité de l’intégrande modèle sur chaque queue ;
- `hderiv_global` : identification différentielle de la primitive modèle.

### Sortie

On obtient un `SpectralData` dont :

- les champs de base sont recopiés ;
- le champ `residualTail` est défini comme la queue intégrale réelle ;
- le champ `hAbelTail` est fourni automatiquement par
  `abelTailEstimate`.
-/
noncomputable def mkSpectralDataFromAbel
    (N w wDeriv : ℝ → ℝ)
    (hZeroDensity : N =O[atTop] (fun T => T * Real.log T))
    (hWeightDecay : w =O[atTop] (fun T => T ^ (-3 : ℤ)))
    (hWeightDerivDecay : wDeriv =O[atTop] (fun T => T ^ (-4 : ℤ)))
    (hIntegrand : (fun t => N t * wDeriv t) =O[atTop] abelIntegrand)
    (hIntegrandInt : ∀ T, IntegrableOn (fun t => N t * wDeriv t) (Ioi T))
    (hModelInt : ∀ T, IntegrableOn abelIntegrand (Ioi T))
    (hderiv_global : ∀ x > 0, HasDerivAt abelPrimitive (abelIntegrand x) x) :
    SpectralData :=
  { N := N
  , w := w
  , wDeriv := wDeriv

    -- Queue intégrale réellement attachée au couple `(N, wDeriv)`.
    -- C’est cette quantité qui alimente ensuite l’analyse spectrale.
  , residualTail := fun T => tailIntegral (fun t => N t * wDeriv t) T

    -- Hypothèses structurelles recopiées telles quelles dans la donnée spectrale.
  , hZeroDensity := hZeroDensity
  , hWeightDecay := hWeightDecay
  , hWeightDerivDecay := hWeightDerivDecay

    -- Contrôle asymptotique de la queue obtenu via le comparateur Abel/T5.
    -- Toute la substance analytique est encapsulée ici.
  , hAbelTail := abelTailEstimate hIntegrand hIntegrandInt hModelInt hderiv_global
  }

end CouretUnification.Analytic.Integration