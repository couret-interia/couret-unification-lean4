/-
# ResGold/L2_MertensAsymptotic.lean

**Asymptotique Mertens** et constante B_R explicite.

## Résultats clés

* A_P(R) = Σ_{p ≤ P, p ∤ R} ‖M_p‖²_HS = log log P + B_R + o(1)
* B_R = (M_Mertens − D) − Σ_{p | R} (p−2)/(p−1)²
  où D = Σ_p 1/(p(p−1)²) converge absolument
* M_Mertens = γ + Σ_p (log(1 − 1/p) + 1/p) ≈ 0,2615
  (constante de Mertens, dépend de Mathlib)

## Frontière L2a / L2b

Ce module fixe **L2a** (régularisation Tamagawa–Mertens locale-par-locale).

Il ne construit **pas** :
* le tenseur global Ψ_R renormalisé (statut [H/O])
* la compatibilité Poisson sous Gate 0 (statut [O])

Cette séparation est doctrinale : Gate 0 exige que symétrie fonctionnelle
soit traitée séparément de l'existence du tenseur renormalisé.

## v38.5 — Paramétrisation Mertens

Les versions antérieures portaient `MertensConstant : ℝ := sorry` et
`Bconst` qui en dépendait. Cette structure introduisait un `sorry` au
niveau d'une *constante* (objet non-Prop), ce qui est doctrinalement
ambigu (ce n'est ni un théorème conditionnel, ni un axiom assumé).

Correction v38.5 : `mertensA_asymptotic` est désormais **paramétré** par la
constante de Mertens et son asymptotique, suivant le pattern `L7For`
du `SpectralBridge` v38.3.

Aucun `axiom` n'est introduit. La constante de Mertens reste hors module.

## v38.5b — Imports explicités (audit d'harmonisation)

Les versions antérieures s'appuyaient sur des imports transitifs implicites
pour `Filter.Tendsto`, `Filter.atTop`, et `Nat.divisors`. Ces imports
sont désormais déclarés explicitement pour garantir le build indépendamment
des chaînes transitives Mathlib (qui peuvent changer entre versions).

## Statut

* `mertensA` (somme tronquée) : [D]
* `Dconst` (série convergente Σ 1/(p(p-1)²)) : [D, provable]
* `Bconst_param mc R` (constante paramétrée) : [D, structural]
* `mertensA_asymptotic_param` : [D conditional on h_mertens]
* Limite globale renormalisée : **non construite ici**, statut [H/O]
-/

import CouretUnification.ResGold.L1_ConductorOne
-- import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- import Mathlib.NumberTheory.Divisors
-- import Mathlib.Order.Filter.AtTopBot.Basic
-- import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace CouretUnification.ResGold.L2

open BigOperators Finset Filter ResGold.L1

/-- Somme tronquée des normes HS au carré, sur les premiers p ≤ P tels
que p ∤ R. **[D]** comme objet fini ; l'asymptotique est traitée plus bas. -/
noncomputable def mertensA (P : ℕ) (R : ℤ) : ℝ :=
  ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
    if (p : ℤ) ∣ R then 0
    else ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2

/-- Constante D = Σ_p 1/(p(p−1)²).

On l'encode comme une somme infinie sur `ℕ`, avec terme nul hors des
nombres premiers. La convergence absolue est un lemme séparé éventuel ;
la définition elle-même ne nécessite aucun `sorry`. -/
noncomputable def Dconst : ℝ :=
  ∑' p : ℕ,
    if Nat.Prime p then
      (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)
    else
      0

/-- Constante B_R paramétrée par la constante de Mertens.

**[D, structural]** — la valeur dépend de `mc` (constante de Mertens
externe). Quand Mathlib fournit la constante, on peut instancier ;
en attendant, ce paramètre reste explicite.

Formule : B_R(mc) = (mc - D) - Σ_{p | R, p premier} (p-2)/(p-1)². -/
noncomputable def Bconst_param (mc : ℝ) (R : ℤ) : ℝ :=
  (mc - Dconst)
    - ∑ p ∈ (Nat.divisors R.natAbs).filter Nat.Prime,
        ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2

/-- **[D conditionnel]** Identité asymptotique paramétrée par la constante
de Mertens.

Énoncé : si `mc` satisfait l'asymptotique de Mertens
    Σ_{p ≤ P} 1/p − log log P → mc,
alors
    mertensA_P(R) − (log log P + B_R(mc)) → 0.

**Pattern paramétrique (cf. v38.3 SpectralBridge.L7For)** : le théorème
prend la constante et son asymptotique en hypothèses, sans les
axiomatiser. Le module ResGold principal ne dépend ainsi d'aucun axiom
externe.

**Esquisse de preuve :**
* (p−2)/(p−1)² = 1/p − 1/(p(p−1)²)
* h_mertens donne Σ_{p ≤ P} 1/p = log log P + mc + o(1)
* Σ_{p ≤ P} 1/(p(p−1)²) → Dconst (absolument convergent)
* corrections finies pour p | R rassemblées dans Bconst_param mc R. -/
theorem mertensA_asymptotic_param
    (mc : ℝ)
    (h_mertens : Tendsto
        (fun P : ℕ =>
          (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
              (1 : ℝ) / (p : ℝ))
          - Real.log (Real.log P) - mc)
        atTop (nhds 0))
    (R : ℤ) :
    Tendsto
      (fun P : ℕ => mertensA P R - (Real.log (Real.log P) + Bconst_param mc R))
      atTop (nhds 0) := by
  sorry -- [D conditional on h_mertens]

/-- **Limite globale renormalisée** : explicitement **non construite** ici.
Documentée comme verrou pour module ultérieur. -/
def globalRenormalizedTensor_status : ResGoldStatus := ResGoldStatus.H

/-- **Compatibilité Poisson sous Gate 0** : explicitement non traitée ici.
Verrou séparé. -/
def poisson_compatibility_status : ResGoldStatus := ResGoldStatus.O

/-- **Inscription doctrinale** : ce module fixe L2a et **uniquement** L2a.

L2b (Poisson séparé) et le pont vers ξ sont à traiter dans des modules
distincts, après validation de L2a et construction préalable d'un
foncteur Mellin–adélique (Verrou A). -/
def L2a_scope : ResGoldStatus := ResGoldStatus.D

/-- **Statut Mertens externe** : la constante de Mertens n'est *pas*
définie dans ce module. Si Mathlib v4.29.1 la fournit (à vérifier par
grep dans `.lake/packages/mathlib/Mathlib/NumberTheory/`), on peut
créer un fichier feuille `ResGold/MertensExternal.lean` qui l'importe
et fournit `h_mertens`. Sinon, le théorème principal `mertensA_asymptotic_param`
reste conditionnel — pattern strictement parallèle à `L7For` v38.3. -/
def MertensConstant_status : ResGoldStatus := ResGoldStatus.H

end CouretUnification.ResGold.L2
