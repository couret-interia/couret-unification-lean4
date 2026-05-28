/-
# ResGold.lean

Fichier-racine du module `ResGold` (sous-programme du programme
Couret–Unification, dossier Expert / ResGold local).

Importe les couches L0, L1, L2 et vérifie l'invariant de compilation `RHClaimed = false`.

## Architecture

```
ResGold.lean                        -- ce fichier
├── ResGold/Status.lean             -- statuts épistémiques + RHClaimed
├── ResGold/L0_LocalLemma.lean      -- AdelicLocalLemma : I_p(R) = ν_p(R)/(p−1)
├── ResGold/L1_ConductorOne.lean    -- opérateur conducteur 1, spectre, HS, trace
└── ResGold/L2_MertensAsymptotic.lean -- mertensA_P(R) = log log P + B_R + o(1) (paramétré)
```

## Doctrine

Aucun fichier de cette hiérarchie n'introduit `axiom`.
Depuis la clôture v38.5, L0–L2 compilent sans `sorry` et sans warning.
Les verrous non construits ne sont pas encodés par des preuves manquantes :
ils sont exposés comme statuts épistémiques (`H` ou `O`) ou comme
hypothèses explicites de théorèmes conditionnels.

L'identification globale `det₂(I − zM) ∼ ξ(½ + iz)` n'est **pas**
formulée dans ce module. Elle relève de modules `VerrouA.lean`,
`VerrouF.lean` à créer ultérieurement après validation L0–L2.

## v38.5 — État après corrections

* Bug `True` placeholders éliminé : `signedTrace_spec` et
  `psi_L2_eq_HSnorm` portent désormais des énoncés substantiels.
* Constante de Mertens paramétrée : `mertensA_asymptotic_param` prend
  l'asymptotique de Mertens en hypothèse, suivant le pattern `L7For`
  v38.3. Aucun `sorry` au niveau d'une constante.
* Import inutile `Mathlib.NumberTheory.Padics.PadicNumbers` retiré de L2.

Voir `RESGOLD_CORRECTIONS_v38.5_NOTE.md` pour le détail des corrections.

## État de compilation attendu (validé par Thomas)

* Compile sans erreur
* Compile sans warning
* Aucun `sorry` attendu dans ResGold L0–L2
* Les dépendances non fermées sont représentées par statuts ou hypothèses nommées
* Aucun axiome
* `#print axioms CouretUnification.ResGold.ResGold_module_does_not_claim_RH` doit retourner
  `does not depend on any axioms`.
  (besoin de `import CouretUnification.ResGold`).

Auteur : programme Couret–Unification.
Façade consolidée validée et dédupliquée par Thomas (Lean 4 / Mathlib v4.29.1).
-/

import CouretUnification.ResGold.Status
import CouretUnification.ResGold.L0_LocalLemma
import CouretUnification.ResGold.L1_ConductorOne
import CouretUnification.ResGold.L2_MertensAsymptotic

namespace CouretUnification.ResGold

/-- Vérification triviale : RHClaimed est false par construction. -/
theorem ResGold_module_does_not_claim_RH : RHClaimed = false := rfl

/-- Statut consolidé des objets de ce module, à des fins documentaires.

Mis à jour v38.5 : les entrées Mertens et signedTrace reflètent la
correction (paramétrisation et énoncés substantiels). -/
def statusTable : List (String × ResGoldStatus) :=
  [ ("nu_value (combinatorial)",                    ResGoldStatus.D)
  , ("Jcal_one, Jcal_nontrivial",                   ResGoldStatus.D)
  , ("Ip_quotient (rational form)",                 ResGoldStatus.D)
  , ("I_p(R) as p-adic integral",                   ResGoldStatus.H)
  , ("M^(1,0) conductorOneEigenvalue_abs_sq",       ResGoldStatus.D)
  , ("HSnorm_sq_eq (definition)",                   ResGoldStatus.D)
  , ("signedTrace_three_cases",                     ResGoldStatus.D)  -- v38.5: replaces True
  , ("signedTrace ↔ spectral sum",                  ResGoldStatus.O)  -- requires Fintype enumeration
  , ("psi_L2_eq_HSnorm (real finite identity)",     ResGoldStatus.D)  -- v38.5: replaces True
  , ("mertensA_P(R) truncated sum",                 ResGoldStatus.D)
  , ("Dconst (tsum object; convergence via h_D)",   ResGoldStatus.D)
  , ("Bconst_param (Mertens-parametric)",           ResGoldStatus.D)  -- v38.5: parametric form
  , ("mertensA_asymptotic_param",                   ResGoldStatus.D)  -- conditional on explicit hypotheses
  , ("MertensConstant (external)",                  ResGoldStatus.H)
  , ("global renormalized tensor",                  ResGoldStatus.H)
  , ("Poisson compatibility (Gate 0)",              ResGoldStatus.O)
  , ("det₂(I − zM) ∼ ξ(½ + iz)",                    ResGoldStatus.O)
  ]

end CouretUnification.ResGold
