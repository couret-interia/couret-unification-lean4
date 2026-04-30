/-
  Couret-Unification — v35.9.1
  Logic/ExplicitFormula/TraceObject.lean

  Objet : RÉCEPTACLE NEUTRE TYPÉ pour la formule explicite.

         En Frozen, c'est seulement un type. Il n'est PAS encore
         identifié à :
           - une somme sur les zéros,
           - un déterminant,
           - une intégrale archimédienne,
           - ou une formule de trace analytique.

  Statut     : Frozen-eligible (0 sorry, 0 axiome local, structures)
  Layer      : Logic.ExplicitFormula
  Dépend de  : Logic.ExplicitFormula.TestPair
  RHClaimed              : false
  HilbertPolyaClaimed    : false
  PhysicalClaimed        : false
  sorryCount             : 0
  axiomCount             : 0

  Ajout v35.9.1 : NOUVEAU FICHIER (PR-2A pur, indépendant de PrimeSide).
                  Les adaptateurs qui dépendent de PrimeSide sont placés
                  dans PrimeSideAsFormulaSide.lean (PR-2B, après build PR-1).

  Pour Bernard.
-/

import CouretUnification.Logic.ExplicitFormula.TestPair

namespace CouretUnification.Logic.ExplicitFormula

/-- Cible neutre pour la voûte de la formule explicite.
    En Frozen, un simple réceptacle typé ℂ-valué. -/
structure TraceObject where
  value : TestPair → ℂ

/-- Side générique de la formule explicite. PrimeSide, ZeroSide,
    ArchimedeanSide et Det2Side exposent tous une valeur commune
    `TestPair → ℂ` sans revendication analytique. -/
structure FormulaSide where
  value : TestPair → ℂ

/-- Obligation typée : un side coïncide avec l'objet trace neutre.
    Pas encore un théorème sur la formule explicite. -/
structure SideEqualsTrace
    (S : FormulaSide) (T : TraceObject) : Prop where
  eq_value : ∀ φ : TestPair, S.value φ = T.value φ

/-- Projection immédiate : deux sides certifiés = Trace sont égaux. -/
theorem sides_equal_of_trace_equal
    {S₁ S₂ : FormulaSide} {T : TraceObject}
    (h₁ : SideEqualsTrace S₁ T) (h₂ : SideEqualsTrace S₂ T) :
    ∀ φ : TestPair, S₁.value φ = S₂.value φ := by
  intro φ
  rw [h₁.eq_value φ, h₂.eq_value φ]

end CouretUnification.Logic.ExplicitFormula
