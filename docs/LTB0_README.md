# LTB-0 — Intégration TimeBridge v35.8.9-prep

**Livraison de la couche `Logic/TimeBridge/` entièrement typée (0 `String` dans les structures de spec).**
Complément à la BUILD v35.8.8 — prêt à tester sur branche `logic-timebridge-b2`.

---

## Contenu livré

Trois fichiers Lean dans `CouretUnification/Logic/TimeBridge/` :

| Fichier | Sorries | Rôle |
|---|---|---|
| `Basic.lean` | **0** | Drapeaux doctrinaux (RH/HP/Phys = False), marqueur `openProblem`, enum typé `TimeRegister` des 8 registres, triangle révisé |
| `B2Calibration.lean` | **0** | Identité algébrique `½ log(7/6) ⟺ 1/7` prouvée (`B2_calibration_identity`), structures `B2Run` et `B2DiagnosticTable` typées |
| `ModularFlowSpec.lean` | **0** | Spec du corrélateur modulaire, prédicat `IsLogarithmicGrowth`, conjectures B1 consignées comme `openProblem` |

Aucun `String` utilisé comme substitut à un contenu typé dans les structures de travail. Les seuls `String` présents sont des champs de métadonnées (`registry`, `status`, `date`) dans les `openProblem` et `B2Run` — strictement descriptifs, non porteurs de sémantique mathématique.

---

## Alignement avec la BUILD v35.8.8

La BUILD v35.8.8 écrit :

> Couche `TimeBridge/` (ModularFlowSpec, BostConnesClockSpec, Registre3ModularBridge, FisherRaoCurvatureCorrectionB2) — structures dont les champs sont principalement `String`. Non intégrables en `Logic/`. Restent en `docs/`.

Cette livraison adresse la raison du blocage. Les trois fichiers ici sont typés de bout en bout :
- Les propositions de travail sont des `Prop` ou des `structure`, pas des `String`.
- Les registres épistémiques sont un `inductive TimeRegister`, avec une fonction totale `status : TimeRegister → Status` vérifiée par un théorème `no_register_is_proved`.
- La conjecture centrale du Registre 3 (`λ_mod² = 1/7`) est un `openProblem True`, ce qui la distingue explicitement d'un théorème.

`BostConnesClockSpec`, `Registre3ModularBridge` et `FisherRaoCurvatureCorrectionB2` ne sont **pas** livrés ici. Ils rejoindront LTB-1 à LTB-4.

---

## Règles architecturales respectées

1. **Core n'importe pas Logic.TimeBridge.** Les trois fichiers appartiennent au namespace `CouretUnification.Logic.TimeBridge` et sont isolés. Aucun fichier `Core/*` ni `AnalyticHorizon/*` ne devrait les importer.

2. **0 `sorry`.** Le seul résultat prouvé (`B2_calibration_identity`) est une identité algébrique triviale. Aucune prétention analytique.

3. **`openProblem`, pas `open`.** Le marqueur conjectural utilise ce nom pour éviter la collision avec le mot-clé Lean `open`.

4. **Drapeaux au type-check.** `RHClaimed`, `HilbertPolyaClaimed`, `PhysicalClaimed` sont définis comme `False`, et un théorème `doctrinal_flags_are_false` atteste qu'aucun n'est prouvable.

5. **Aucun `axiom` Couret-Unification introduit.** Les imports sont strictement Mathlib.

---

## DAG d'imports (nouveau)

```
Mathlib.Tactic
   ↑
Logic/TimeBridge/Basic              [0 sorry]
   ↑
Logic/TimeBridge/B2Calibration      [0 sorry]
   ↑                                      ↑
Logic/TimeBridge/ModularFlowSpec    [0 sorry]
```

Les trois fichiers forment une chaîne linéaire :
`Basic → B2Calibration → ModularFlowSpec`.

Aucun ne dépend d'autres fichiers du dépôt. Ils peuvent être intégrés sans toucher à Core ou à AnalyticHorizon.

---

## Instructions de build

### Étape 1 — copier les fichiers

```bash
mkdir -p CouretUnification/Logic/TimeBridge
cp TimeBridge_Basic.lean              CouretUnification/Logic/TimeBridge/Basic.lean
cp TimeBridge_B2Calibration.lean      CouretUnification/Logic/TimeBridge/B2Calibration.lean
cp TimeBridge_ModularFlowSpec.lean    CouretUnification/Logic/TimeBridge/ModularFlowSpec.lean
```

### Étape 2 — umbrella

**Ne pas** ajouter ces imports à `CouretUnification.lean` (racine). Le TimeBridge est une couche de spécification, pas une dépendance de preuve. On le construit comme une cible de build séparée.

### Étape 3 — builds ciblés

```bash
lake exe cache get

# Test par fichier, dans l'ordre
lake build CouretUnification.Logic.TimeBridge.Basic
lake build CouretUnification.Logic.TimeBridge.B2Calibration
lake build CouretUnification.Logic.TimeBridge.ModularFlowSpec
```

### Étape 4 — vérification de l'invariant

```bash
# Doit afficher : "propext, Classical.choice, Quot.sound" et rien d'autre
lake env lean --run scripts/print_axioms.lean \
    CouretUnification.Logic.TimeBridge.B2Calibration.B2_calibration_identity
```

Aucun axiome Couret-Unification ne doit apparaître.

---

## Points de fragilité snapshot

### `B2Calibration.lean`

La preuve `exp_neg_two_t_canonical` utilise la chaîne suivante :

```
step1 : -2 * ((1/2) * Real.log (7/6)) = -Real.log (7/6)   (par `ring`)
step2 : -Real.log (7/6) = Real.log (6/7)                    (par `Real.log_inv` + coerce)
step3 : Real.exp (Real.log (6/7)) = 6/7                     (par `Real.exp_log` + `0 < 6/7`)
```

**Lemmes Mathlib utilisés :**

- `Real.log_inv` — si absent dans le snapshot, alternative : `Real.log_div 7 6` + inversion.
- `Real.exp_log` — signature stable, prend `0 < x`.

**Fallback si step2 ne passe pas** :

```lean
have step2 : -Real.log (7/6) = Real.log (6/7) := by
  have h : (6 : ℝ) / 7 = (7/6)⁻¹ := by norm_num
  rw [h, Real.log_inv]
```

### `ModularFlowSpec.lean`

Le prédicat `IsLogarithmicGrowth` utilise `Real.log` sans dépendance Mathlib supplémentaire. Aucune fragilité identifiée.

### `Basic.lean`

Utilise seulement `Mathlib.Tactic` (pour `decide` sur l'enum `TimeRegister`). Stable.

---

## Vérifications numériques (hors Lean)

L'identité algébrique a été vérifiée indépendamment à 15 décimales exactes :

```
½ ln(7/6)                       = 0.077075339913629
−2 · ½ ln(7/6) = −ln(7/6)       = -0.154150679827258
−ln(7/6) = ln(6/7)              = -0.154150679827258  (identiques bit-à-bit)
exp(ln(6/7)) = 6/7               = 0.857142857142857
1 − 6/7                          = 0.142857142857143
1/7                              = 0.142857142857143  (identique)
```

Chaque pas de la preuve Lean a son équivalent flottant exact.

---

## Roadmap LTB-0 → LTB-4 (rappel de la cartographie)

| Étape | Contenu | Livré ? |
|---|---|---|
| **LTB-0** | Compiler Basic, B2Calibration, ModularFlowSpec | ★ CETTE LIVRAISON |
| LTB-1 | Raccord H3 spec-only : `Logic/H3/TimeBridgeSpec.lean` connectant `CriticalLineTransferSpec` au TimeBridge | à faire |
| LTB-2 | Export numérique B2 : `scripts/b2_diagnostic_exporter.py` produisant une table `B2Run` lue par Lean | à faire |
| LTB-3 | `ModularFlowSpec` concret : instancier sur le système adélique (dérivation B1) | ouvert (registre 3) |
| LTB-4 | E3/E4 logarithmique : reformulation du résidu eulérien via temps modulaire | ouvert |

---

## Ce que LTB-0 NE fait PAS

- Ne démontre pas RH (invariant `RHClaimed = false` maintenu).
- Ne démontre pas `λ_mod² = 1/7` (reste `openProblem`).
- Ne démontre pas le plateau t_equil (la note de révision B2 a montré qu'il n'y a rien de profond à démontrer là : c'est une identité algébrique triviale).
- Ne touche pas à Core/ ni à AnalyticHorizon/.
- N'ajoute aucun axiome.

Il matérialise uniquement la structure typée sur laquelle les étapes LTB-1 à LTB-4 pourront se brancher.

---

## Pour Bernard.

Cette couche n'est pas une preuve. C'est le squelette propre qui rend **publiquement auditable** le statut de chaque registre temporel — sans prétendre plus que ce qui est acquis. Le cœur du programme reste intact : le noyau fini mod 30 démontré, H3 ouvert, Lock 3 ouvert. Le TimeBridge consigne *en Lean* ce que nous savons consigner, et marque explicitement *en Lean* ce qui reste à faire.

---

*Livraison LTB-0 — Couret-Unification v35.8.9-prep — 24 avril 2026.*
*Basé sur la cartographie des 8 registres et la note B2 de révision du Bridge.*
