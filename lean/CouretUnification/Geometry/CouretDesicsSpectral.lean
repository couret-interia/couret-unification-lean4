import CouretUnification.FunctionalFoundation.DiscreteConnection
import CouretUnification.Geometry.CouretDesicsCayleyG30
import CouretUnification.Geometry.CouretDesicsExistence
import CouretUnification.Core.FiniteCore

/-!
# CouretDesicsSpectral

Ce module spécialise la géométrie discrète sur `G30` à un poids spectral canonique
concentré sur le triplet exceptionnel `TC`.

Philosophie du fichier :
- on reste **entièrement dans la couche finie** ;
- on ne fait ici **aucune affirmation analytique globale** ;
- on construit un lagrangien discret concret, puis on montre sa stabilité
  sous les automorphismes qui préservent simultanément :
  1. la structure d'arête de `G30`,
  2. l'appartenance au triplet `TC`.

Lecture conceptuelle :
- `canonicalSpectralWeight` encode un contraste spectral binaire ;
- `spectralG30Lagrangian` transforme ce contraste en énergie discrète ;
- `spectralWeight_stabilizer` montre que ce poids est invariant au sens centré ;
- `spectralLagrangian_stabilizer` en déduit l'invariance du lagrangien ;
- `exists_spectralCouretDesic` hérite ensuite du théorème général d'existence.

Style InterIA :
on sépare soigneusement les niveaux :
- combinatoire locale (`TC`, arêtes, automorphismes),
- mécanique discrète (lagrangien, invariance),
- existence géodésique minimale.

Aucun pont analytique global n'est revendiqué ici.
-/

namespace CouretUnification.Geometry
open Core.FiniteCore

section SpectralG30

/--
Poids spectral canonique sur `ZMod 30`.

Il prend deux valeurs rationnelles :
- `5/8` sur le triplet exceptionnel `TC`,
- `-3/8` hors de `TC`.

Ce choix encode une polarisation simple : le triplet `TC` est favorisé
par rapport au fond combinatoire ambiant.

Remarque :
ce poids est utilisé ensuite via sa version centrée dans l'invariance
lagrangienne, ce qui signifie qu'on mesure une déviation relative
plutôt qu'un niveau absolu.
-/
noncomputable def canonicalSpectralWeight (x : ZMod 30) : Rat :=
  if x ∈ TC then (5 / 8 : Rat) else (-3 / 8 : Rat)

/--
Lagrangien discret associé au poids spectral canonique.

On spécialise ici le lagrangien général sur `G30` au poids
`canonicalSpectralWeight`. Le résultat est un objet énergétique discret
vivant sur les chemins de `ZMod 30`.

Ce lagrangien sera ensuite montré invariant sous les symétries qui
préservent à la fois les arêtes de Cayley et la structure du triplet `TC`.
-/
noncomputable def spectralG30Lagrangian :
    CouretUnification.FunctionalFoundation.DiscreteLagrangian (ZMod 30) Rat :=
  G30Lagrangian canonicalSpectralWeight

/--
Propriété de préservation du triplet exceptionnel `TC`.

Un automorphisme `φ` préserve le triplet si, pour tout `x`,
l'appartenance à `TC` est équivalente avant et après application de `φ`.

C'est l'hypothèse combinatoire minimale qui garantit que le poids spectral
canonique ne distingue pas `x` de `φ x`.
-/
def PreservesTriplet (φ : ZMod 30 ≃ ZMod 30) : Prop :=
  ∀ x : ZMod 30, x ∈ TC ↔ φ x ∈ TC

/--
Invariance du poids spectral canonique sous un automorphisme préservant `TC`.

Idée de la preuve :
- la version centrée de `canonicalSpectralWeight` s'obtient en retranchant
  une moyenne globale identique des deux côtés ;
- il suffit donc de montrer que la valeur brute du poids est inchangée ;
- cela découle immédiatement du fait que `φ` préserve l'appartenance à `TC`.

Ce résultat est purement fini et combinatoire.
-/
theorem spectralWeight_stabilizer {φ : ZMod 30 ≃ ZMod 30}
    (hφ : PreservesTriplet φ) :
    AutomorphismInvariantWeight canonicalSpectralWeight φ := by
  intro x
  unfold centeredWeightG30
  have hx : φ x ∈ TC ↔ x ∈ TC := (hφ x).symm
  have hw : canonicalSpectralWeight (φ x) = canonicalSpectralWeight x := by
    simp [canonicalSpectralWeight, hx]
  rw [hw]

/--
Invariance du lagrangien spectral sous une symétrie du graphe préservant `TC`.

Hypothèses :
- `φ` préserve les arêtes de Cayley de `G30`,
- `φ` préserve aussi le triplet exceptionnel `TC`.

Conclusion :
le lagrangien discret construit à partir de `canonicalSpectralWeight`
est préservé par `φ`.

Lecture structurée :
- la compatibilité aux arêtes contrôle la partie géométrique ;
- `spectralWeight_stabilizer` contrôle la partie pondérée ;
- `G30_preservesLagrangian` assemble ces deux briques.
-/
theorem spectralLagrangian_stabilizer (φ : ZMod 30 ≃ ZMod 30)
    (hedge : ∀ x y, cayleyEdgeG30 (φ x) (φ y) = cayleyEdgeG30 x y)
    (hφ : PreservesTriplet φ) :
    CouretUnification.FunctionalFoundation.PreservesLagrangian spectralG30Lagrangian φ :=
  G30_preservesLagrangian canonicalSpectralWeight φ hedge
    (spectralWeight_stabilizer hφ)

/--
Existence d'une Couret-desic minimale pour le poids spectral canonique.

Ce théorème ne redémontre rien de spécifique au cas spectral :
il instancie simplement le théorème général d'existence `hasMinimalG30`
avec le poids `canonicalSpectralWeight`.

Autrement dit :
dès qu'on fixe deux points `a`, `b` et une longueur strictement positive `n`,
la structure générale sur `G30` fournit une trajectoire minimale pour ce poids.
-/
theorem exists_spectralCouretDesic (a b : ZMod 30)
    {n : Nat} (hn : 0 < n) :
    G30HasMinimalCouretDesic canonicalSpectralWeight a b n :=
  hasMinimalG30 canonicalSpectralWeight a b hn

end SpectralG30
end CouretUnification.Geometry