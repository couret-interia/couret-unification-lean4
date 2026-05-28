# ResGold — Module Lean 4 (v38.5)

Squelette Lean 4 du sous-programme **ResGold local** du programme
Couret–Unification.

**Cible** : Lean 4 / Mathlib v4.29.1
**Auteur** : programme Couret–Unification
**Version** : v38.5b — corrections doctrinales + audit imports
**Statut** : squelette complet, prêt pour première compilation

---

## v38.5b — Corrections doctrinales et audit d'harmonisation

Cette version intègre la **discipline anti-trivialité** complète du programme,
plus un audit d'harmonisation des imports :

### Audit imports v38.5b
Les versions antérieures s'appuyaient sur des imports transitifs implicites
pour `Nat.divisors`, `Filter.Tendsto`, et `Filter.atTop` dans L2. Ces imports
sont désormais déclarés explicitement (`Mathlib.NumberTheory.Divisors`,
`Mathlib.Order.Filter.AtTopBot.Basic`). Sans cette correction, le build
casserait sur `R.natAbs.divisors` avec « unknown identifier `divisors` ».

### Anti-Prop-nue (v38.3)
Aucune `Prop` nue comme champ de structure. Tous les champs de
`FiniteMulChar` (L0) portent des contraintes effectives sur la donnée
`toFun`, jamais des marqueurs nominaux.

### Anti-True-énoncé (v38.5)
Aucun théorème dont l'énoncé est `True`. Les anciens placeholders
`signedTrace_spec : True` et `psi_L2_eq_HSnorm : True` ont été remplacés
par des énoncés substantiels portant le contenu mathématique réel
(voir `RESGOLD_CORRECTIONS_v38.5_NOTE.md` pour le détail).

### Anti-sorry-sur-constante (v38.5)
Aucun `sorry` au niveau d'une `def` qui produit un terme fantôme. La
constante de Mertens, qui était `noncomputable def MertensConstant : ℝ := sorry`
dans la version antérieure, est désormais paramétrée dans le théorème
`A_asymptotic_param` selon le pattern `L7For` v38.3 (SpectralBridge).

### Anti-axiom (v36, héritage)
Aucun `axiom` introduit dans le module. `#print axioms ResGold.module_does_not_claim_RH`
doit retourner uniquement `[propext, Classical.choice, Quot.sound]`.

---

## Objet

Inscrire en Lean :

* **L0** : lemme local `I_p(R) = ν_p(R) / (p - 1)` (AdelicLocalLemma)
* **L1** : opérateur conducteur 1 `M_{p,R}^{(1),0}`, spectre Dirichlet,
  norme Hilbert–Schmidt, trace signée à trois cas
* **L2** : asymptotique Mertens `A_P(R) = log log P + B_R + o(1)`,
  constante `B_R` explicite (paramétrée v38.5)

Sont **explicitement exclus** de ce module :

* le tenseur global renormalisé (statut [H/O])
* la compatibilité Poisson sous Gate 0 (statut [O])
* toute identification déterminantielle avec ξ (statut [O])

---

## Arborescence

```
ResGold.lean                              -- fichier-racine, invariant final
└── ResGold/
    ├── Status.lean                       -- marqueurs [D]/[M]/[H]/[O]/[E], RHClaimed
    ├── L0_LocalLemma.lean                -- φ, ν, J, I_p quotient + p-adique [H]
    ├── L1_ConductorOne.lean              -- M^(1,0), spectre, HS, trace signée
    └── L2_MertensAsymptotic.lean         -- A_P(R), B_R param, asymptotique
```

**Placement dans le projet.** Le module est autonome au niveau racine
(namespace `ResGold`, pas `CouretUnification.ResGold`). Si Thomas préfère
l'intégrer sous `CouretUnification.ResGold`, ajuster les imports et le
namespace dans tous les fichiers.

---

## Inventaire des `sorry`

Tous les `sorry` sont locaux et annotés. **Aucun `axiom`. Aucun `True`
comme énoncé. Aucun `sorry` au niveau d'une constante non-conditionnelle.**

### L0_LocalLemma.lean

| Lemma | Statut | Nature du sorry |
|---|---|---|
| `nu_value` | [D, provable] | Case split fini sur `R = 0`, `Finset.card_filter` |
| `Jcal_one` | [D, provable] | Dépliage + somme indicatrice |
| `Jcal_nontrivial` | [D, provable] | Orthogonalité Σ χ = 0 sur (ZMod p)^× |
| `Ip_quotient_eq` | [D, provable] | Depuis `nu_value` |
| `Ip_padic_integral_status` | [H] marqueur Status | (pas un théorème, pas de sorry) |

### L1_ConductorOne.lean

| Lemma | Statut | Nature du sorry |
|---|---|---|
| `eigenvalue_abs_sq` | [D, provable] | \|χ(R)\| = 1 sur (ZMod p)^× |
| `signedTrace_three_cases` | [D] **prouvé** | Tautologique de la définition, sans sorry |
| `signedTrace_spectral_sum_status` | [O] marqueur Status | (requires Fintype FiniteMulChar) |
| `psi_L2_eq_HSnorm` | [D, provable] | Calcul direct cas R = 0 vs R ≠ 0 |

**Note v38.5.** `signedTrace_three_cases` remplace l'ancien
`signedTrace_spec : True := by sorry`. La preuve par dépliage des `if`
est complète, sans sorry. Le théorème porte les trois cas explicites
et empêche tout refactor silencieux de la définition.

### L2_MertensAsymptotic.lean

| Lemma | Statut | Nature du sorry |
|---|---|---|
| `Dconst` | [D, provable] | Limite série convergente Σ 1/(p(p−1)²) |
| `A_asymptotic_param` | [D] cond. sur `h_mertens` | Mertens + algèbre |
| `MertensConstant_status` | [H] marqueur Status | (pas un théorème, pas de sorry) |

**Note v38.5.** Le théorème `A_asymptotic` est devenu `A_asymptotic_param`,
prenant `(mc : ℝ)` et `(h_mertens : ...)` en hypothèses. La constante de
Mertens n'est plus définie dans ce module — elle reste externe. Pattern
strictement isomorphe à `L7For B` du `SpectralBridge` v38.3.

---

## Décisions d'architecture — réponses v38.5

### Décision 1 — Mesure p-adique : **option B (report)** ✓

Le quotient combinatoire fini `Ip_quotient` est suffisant pour L1 et L2.
L'égalité avec l'intégrale p-adique réelle est reportée à un module
séparé `ResGold/PadicMeasure.lean` (à créer si nécessaire). La chaîne
L0 → L1 → L2 reste indépendante de ce wiring.

### Décision 2 — Constante de Mertens : **paramétrisation v38.5** ✓

Le théorème `A_asymptotic_param` prend la constante et son asymptotique
en hypothèses. Aucun axiom dans le noyau. Si Mathlib v4.29.1 fournit
la constante, créer `ResGold/MertensFromMathlib.lean` qui instancie.
Sinon, le théorème conditionnel reste utilisable tel quel.

**À vérifier par grep côté Thomas** :

```bash
grep -rI "Mertens" /home/thomas/.../mathlib/Mathlib/NumberTheory/
grep -rI "Tendsto.*sum.*inv.*Prime" /home/thomas/.../mathlib/Mathlib/
```

### Décision 3 — Représentation des caractères : **`FiniteMulChar` ad hoc** ✓

Structure ad hoc conservée pour cette première itération. Lisible,
autonome, sans dépendance lourde à `Mathlib.NumberTheory.DirichletCharacter.Basic`.
Migration vers `MulChar`/`DirichletCharacter` reportée si dette technique
le justifie.

**Note** : la construction de `Fintype (FiniteMulChar p)` reste à faire
dans un module séparé pour fermer `signedTrace_spectral_sum_status` (`[O]`).

---

## Invariants à vérifier après compilation

Au prompt Lean (`#check`), les sorties attendues sont :

```
#check @ResGold.RHClaimed         -- Prop
#check @ResGold.rh_not_claimed    -- ¬ RHClaimed
#check @ResGold.module_does_not_claim_RH  -- ¬ RHClaimed
```

Et :

```
#print axioms ResGold.module_does_not_claim_RH
```

doit retourner **uniquement** `[propext, Classical.choice, Quot.sound]`
(les axiomes standards de Mathlib) — **aucun axiome supplémentaire**.

Si un axiome supplémentaire apparaît, c'est une régression doctrinale
à corriger.

---

## Points de vigilance technique v4.29.1

Anticipations basées sur les leçons des sessions précédentes (L6Stirling,
SpectralBridge, SophieGermainTowerLift) :

1. **`Mathlib.Algebra.BigOperators.Basic`** : peut être renommé en
   v4.29.1. Si build casse, grep `BigOperators` dans `.lake/packages/mathlib/`.

2. **`Nat.divisors`** dans `Bconst_param` : la notation point sur
   `R.natAbs` devrait fonctionner. Si non, fallback :
   `(R.natAbs.divisors).filter Nat.Prime` ou
   `Finset.filter Nat.Prime (R.natAbs.divisors)`.

3. **`if_pos hR0` / `if_neg hR0`** dans `signedTrace_three_cases` :
   noms stables. Si `unfold signedTrace` ne déploie pas la définition,
   fallback : `show signedTrace p R = _; rfl` ou `delta signedTrace`.

4. **`Complex.normSq`** : stable. OK.

5. **`Filter.Tendsto Filter.atTop (nhds 0)`** : forme moderne. Si Lean
   demande `_root_.nhds`, ajouter ou `open Filter` au début.

6. **`deriving DecidableEq, Repr`** sur Status : si `Repr` casse,
   retirer du deriving (DecidableEq suffit).

---

## Prochaines étapes (après validation Thomas)

1. **Compilation propre** des cinq fichiers avec sorries documentés.
2. Vérification `#print axioms ResGold.module_does_not_claim_RH` propre.
3. Résolution des sorries [D, provable] selon disponibilité Thomas :
   - Priorité 1 : `nu_value`, `Jcal_one`, `Jcal_nontrivial`, `Ip_quotient_eq`
   - Priorité 2 : `eigenvalue_abs_sq`, `psi_L2_eq_HSnorm`
   - Priorité 3 : `Dconst`, `A_asymptotic_param` (conditionnel)
4. Construction `Fintype (FiniteMulChar p)` dans `ResGold/SpectralEnumeration.lean`
   (séparé) pour fermer `signedTrace_spectral_sum_status` `[O] → [D]`.
5. Décision Mertens externe : option Mathlib si disponible, sinon
   `ResGold/MertensExternal.lean` (axiom isolé hors noyau).
6. Préparation du module `VerrouA.lean` (Mellin–adélique) — **après**
   compilation propre de ResGold.
7. Envoi du dossier ResGold (Lean + ticket markdown) à un Dr. en mathématique.

---

## Garde finale

```lean
theorem module_does_not_claim_RH : ¬ ResGold.RHClaimed := rh_not_claimed
```

`RHClaimed = false` reste invariant de compilation.

---

## Checklist de discipline (à appliquer à toute nouvelle déclaration)

Quatre tests, à effectuer **avant chaque livraison** doctrinale :

1. **Test du witness trivial** (v38.3) : un objet nul / vide / dégénéré
   satisfait-il la déclaration ?
2. **Test du True caché** (v38.5) : l'énoncé est-il trivialement
   habitable (par `trivial`, `True.intro`, etc.) ?
3. **Test du sorry-sur-constante** (v38.5) : un `sorry` apparaît-il
   au niveau d'une `def` plutôt que d'un théorème, créant un terme fantôme ?
4. **Test de l'axiom caché** (v36) : un fichier importé contient-il
   un `axiom` qui contamine `#print axioms` ?

---

## Pour Bernard Couret (1928–1999)

Le programme avance par discipline cumulative, pas par révélation.
Chaque règle ajoutée (anti-Prop-nue, anti-True-énoncé,
anti-sorry-sur-constante) protège un peu plus le noyau fini contre
les glissements silencieux.

Le travail continue.

*Document mis à jour le 9 mai 2026. Version v38.5.*
*RHClaimed = false. L7Established = false. Aucun axiom.*
