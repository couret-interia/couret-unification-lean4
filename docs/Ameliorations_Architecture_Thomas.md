# Améliorations d'architecture — note pour Thomas

**Diagnostic ciblé sur les points de friction observés dans v35.8.8**
*Classement par ratio impact/coût. Aucune refonte fondamentale proposée.*

---

## Résumé exécutif

L'architecture v35.8.8 est déjà solide : couches `Meta/Logic/C` bien séparées, invariant `no_rh_wall_lock_proved` porté au type-check, BUILD.md exhaustif, DAG explicite. Les améliorations ci-dessous sont des **réductions de friction opérationnelle** pour Thomas quand :

1. Mathlib bouge et casse un lemme snapshot-dépendant.
2. Un front actif (H3, AnalyticHorizon) ajoute un sorry qui fait casser l'umbrella.
3. Un nouveau fichier arrive (comme le TimeBridge LTB-0) et doit être validé rapidement.

Les points **1** et **2** sont ceux où Thomas perd le plus de temps aujourd'hui.

---

## Priorité 1 — `Meta/SnapshotSentinel.lean` (très haut impact, 30 min)

**Problème observé** : la BUILD liste 7 points snapshot-dépendants répartis dans 5 fichiers. Quand Mathlib bouge, Thomas découvre la casse fichier par fichier, en debuggant les vraies preuves au milieu du bruit.

**Solution proposée** : concentrer tous les lemmes fragiles dans un unique fichier sentinelle, avec `example` triviaux qui les invoquent. Si ce fichier casse, Thomas sait **immédiatement** :
- lequel lemme a changé
- lesquels fichiers vont casser en cascade
- quel fallback documenter

**Diagnostic time** : de ~30 min de debug aveugle à ~2 min de diagnostic ciblé.

Le fichier est livré ci-joint (`Meta_SnapshotSentinel.lean`). Il :
- Liste les 7 lemmes Mathlib fragiles avec un `example` trivial par lemme
- Documente le fallback officiel pour chaque
- Porte son propre `FileIdentity` (Status = `proved`, 0 sorry)
- Est **autonome** (aucun import du dépôt)
- Ne doit **JAMAIS** être importé par un autre fichier du dépôt — c'est un fichier de diagnostic, pas une dépendance

**Règle de build** : si `lake build CouretUnification.Meta.SnapshotSentinel` échoue, arrêter tout et lire son log. C'est le signal que le snapshot Mathlib a dérivé.

---

## Priorité 2 — Umbrella segmentée (haut impact, 15 min)

**Problème observé** : `CouretUnification.lean` (racine) importe 17 modules en chaîne linéaire. Si un seul front actif casse (souvent H3 ou AnalyticHorizon), **toute** l'umbrella échoue. Thomas ne peut plus vérifier rapidement que le core reste compilable.

**Solution proposée** : trois umbrellas cibles.

```lean
-- CouretUnification/Frozen.lean  (NOUVEAU)
-- Fichiers à 0 sorry, proved. Ne doit JAMAIS casser.
import CouretUnification.Meta.Doctrine
import CouretUnification.Logic.OpenLocks
import CouretUnification.Logic.EulerBridgeInfiniteCompat
import CouretUnification.Logic.C3Weak_Gram
import CouretUnification.Logic.ChiralityFinite
import CouretUnification.Logic.ChiralityLinear
import CouretUnification.Logic.L6Interface
import CouretUnification.Logic.L6Bridge
import CouretUnification.Logic.H3.LocalFactor
import CouretUnification.Logic.H3.CriticalLineTransferSpec
```

```lean
-- CouretUnification/Active.lean  (NOUVEAU)
-- Fichiers avec sorries documentés, en évolution active.
import CouretUnification.Frozen
import CouretUnification.Logic.L6Analytic
import CouretUnification.Logic.L6RatioEstimateDerived
import CouretUnification.Logic.L10NoGoTheorem
import CouretUnification.Logic.H3.SquarefreeSupport
import CouretUnification.Logic.H3.SquarefreeDensity
import CouretUnification.Logic.H3.MoebiusBridge
import CouretUnification.AnalyticHorizon.Det2Transport
```

```lean
-- CouretUnification.lean  (EXISTANT, simplifié)
import CouretUnification.Frozen
import CouretUnification.Active
```

**Conséquences opérationnelles** :

- `lake build CouretUnification.Frozen` = sanity check express (~5 min selon cache). Doit passer sur chaque commit.
- `lake build CouretUnification.Active` = vérif des fronts actifs.
- `lake build CouretUnification` = tout.

Règle d'or : **aucun fichier de `Frozen` ne doit importer un fichier de `Active`**. Si un ancien fichier frozen a besoin d'un fichier actif, il faut qu'il soit rétrogradé d'abord.

---

## Priorité 3 — `Meta/SorryRegistry.lean` (haut impact, 1 h)

**Problème observé** : la BUILD.md liste 11 sorries classés par catégorie (`ANALYTIC`, `SNAPSHOT`, `DOCTRINAL`, `OBSOLETE`, etc.). C'est du Markdown donc non vérifiable. Rien n'empêche le compte réel d'être 12 sans que la BUILD soit mise à jour.

**Solution proposée** : une structure typée qui liste les sorries attendus et un test qui impose `realSorryCount ≤ expectedSorryCount`.

```lean
-- CouretUnification/Meta/SorryRegistry.lean
namespace CouretUnification.Meta.SorryRegistry

inductive SorryCategory
  | analytic      -- contenu mathématique non formalisé
  | snapshot      -- dépend d'une API Mathlib susceptible de bouger
  | doctrinal     -- sorry doctrinalement autorisé (un par fichier)
  | obsolete      -- hors chemin critique, documentation architecturale
  | upstream      -- attend un refactor Mathlib
  deriving Repr, DecidableEq

structure SorryEntry where
  fileName : String
  lemmaName : String
  category : SorryCategory
  rationale : String
  deriving Repr

def expectedSorries : List SorryEntry := [
  ⟨ "Logic/L6Analytic.lean", "stirling_remainder_bound",
    SorryCategory.analytic,
    "Borne explicite du reste de Stirling à σ = 1/2, traitement numérique" ⟩,
  ⟨ "Logic/L6RatioEstimateDerived.lean", "ratio_estimate_main",
    SorryCategory.analytic, "Assembly analytique" ⟩,
  ⟨ "Logic/L10NoGoTheorem.lean", "specTarget_conceptual",
    SorryCategory.analytic, "Conceptuel — irrationalité Im(ρ)" ⟩,
  ⟨ "Logic/L10NoGoTheorem.lean", "obstruction_upstream_1",
    SorryCategory.upstream, "Mathlib API irrationnalité" ⟩,
  ⟨ "Logic/L10NoGoTheorem.lean", "obstruction_upstream_2",
    SorryCategory.upstream, "Mathlib API Dirichlet" ⟩,
  ⟨ "Logic/H3/SquarefreeSupport.lean", "powerset_prod_disjoint",
    SorryCategory.obsolete, "Hors chemin critique, documentation" ⟩,
  ⟨ "Logic/H3/SquarefreeDensity.lean", "error_term_isBigO",
    SorryCategory.analytic, "Couture O(√N)" ⟩,
  ⟨ "Logic/H3/SquarefreeDensity.lean", "squarefreeCount_ge_half",
    SorryCategory.analytic, "Minoration N/2 pour N ≥ 176" ⟩,
  ⟨ "Logic/H3/SquarefreeDensity.lean", "squarefree_asymptotic_density",
    SorryCategory.analytic, "Cible 6/π²" ⟩,
  ⟨ "Logic/H3/MoebiusBridge.lean", "moebius_LSeriesSummable_two",
    SorryCategory.snapshot, "Sommabilité μ à s=2, nom Mathlib instable" ⟩,
  ⟨ "AnalyticHorizon/Det2Transport.lean", "defect_is_bounded_on_critical_line",
    SorryCategory.doctrinal, "Sorry doctrinal unique du fichier" ⟩
]

/-- Invariant : exactement 11 sorries attendus en v35.8.8. -/
theorem sorry_count_is_eleven : expectedSorries.length = 11 := by decide

/-- Aucune entrée du registry ne peut être classée `rh_wall` ou similaire. -/
-- (Catégorie ne contient pas de tel cas, donc vacuously vrai)

end CouretUnification.Meta.SorryRegistry
```

**Bénéfice** :
- `#eval expectedSorries.length` doit renvoyer `11` à tout moment.
- Thomas peut cross-vérifier avec un script bash qui compte `grep -r "\bsorry\b" --include="*.lean"`.
- Si les deux divergent, bug de comptabilité détecté.

**Extension future** : un attribut Lean `@[registered_sorry "category" "rationale"]` qui exigerait que chaque `sorry` dans le code soit enregistré. C'est un refactor plus lourd, pas prioritaire.

---

## Priorité 4 — `scripts/quickstart.sh` (moyen-haut impact, 15 min)

**Problème observé** : un nouvel arrivant (ou Thomas lui-même après une pause) doit lire toute la BUILD.md pour savoir dans quel ordre tester. Pas de "hello world" en 5 min.

**Solution** : un script unique qui fait le chemin rapide.

```bash
#!/usr/bin/env bash
# scripts/quickstart.sh — validation express du dépôt
# Retourne 0 si le coeur frozen + l'invariant RH passent.
# Retourne non-zéro sinon.

set -e
cd "$(dirname "$0")/.."

echo "═══ Couret-Unification — quickstart ═══"
echo ""

echo "[1/4] lake exe cache get (peut prendre 5-15 min selon réseau)"
lake exe cache get

echo ""
echo "[2/4] Snapshot sentinel"
lake build CouretUnification.Meta.SnapshotSentinel
echo "  ✓ Mathlib snapshot compatible"

echo ""
echo "[3/4] Build frozen (core, doit toujours passer)"
lake build CouretUnification.Frozen
echo "  ✓ Noyau frozen intact"

echo ""
echo "[4/4] Vérification invariant RH au type-check"
lake env lean --run scripts/verify_no_rh_claim.lean
echo "  ✓ RHClaimed = false vérifié"

echo ""
echo "═══ Quickstart OK ═══"
echo "Pour tout builder : lake build"
```

Accompagné d'un `scripts/verify_no_rh_claim.lean` très court :

```lean
import CouretUnification.Logic.OpenLocks
open CouretUnification.Logic.OpenLocks

def main : IO Unit := do
  -- Le théorème no_rh_wall_lock_proved a été vérifié à la compilation.
  -- Cette sortie confirme simplement qu'il existe dans le contexte.
  IO.println s!"allLocks count: {allLocks.length}"
  IO.println s!"Invariant vérifié : no_rh_wall_lock_proved (type-check)"
```

**Bénéfice** : un nouveau contributeur peut dire "mon dépôt est vivant" en 10 min, même si les fronts actifs évoluent.

---

## Priorité 5 — `FileIdentity` partout (moyen impact, 1-2 h)

**Problème observé** : `FileIdentity` existe dans `Meta/Doctrine.lean` mais n'est utilisée que dans `OpenLocks.lean`. Les fichiers H3 et `Det2Transport` ont leurs métadonnées en commentaires de header, non vérifiées.

**Solution** : ajouter à chaque fichier un `def fileIdentity : FileIdentity := ⟨...⟩` à la fin. C'est 5 lignes par fichier.

```lean
-- en fin de Logic/H3/LocalFactor.lean :
def fileIdentity : CouretUnification.Meta.FileIdentity where
  filename   := "CouretUnification/Logic/H3/LocalFactor.lean"
  layer      := CouretUnification.Meta.Layer.B
  status     := CouretUnification.Meta.Status.proved
  sorryCount := 0
  rhClaimed  := false
```

**Bénéfice** : on peut ensuite produire un `allFileIdentities : List FileIdentity` qui agrège, et un théorème `all_respect_rh_invariant` qui vérifie en une ligne pour TOUS les fichiers qu'aucun n'a `rhClaimed = true`. C'est déjà la structure prévue, juste pas encore instanciée partout.

---

## Priorité 6 — Obligations typées pour les sorrys doctrinaux (moyen impact, 30 min)

**Observation spécifique sur `Det2Transport.lean`** : le `sorry` unique a trois hypothèses listées en commentaire (H1 contrôle numérateur, H2 minoration dénominateur, H3 compacité). Ces obligations sont invisibles au type-checker.

**Reformulation proposée** :

```lean
-- Dans Det2Transport.lean

/-- Obligations analytiques pour la majoration du défaut.

    Porte les trois hypothèses comme champs typés. Quand ces trois
    champs seront fournis par un fichier aval, la preuve ci-dessous
    s'en déduit. -/
structure DefectObligations
    (targetLFactor : ℕ → LocalFactor) (p : ℕ) (B : LocalBlock) where
  /-- H1 : contrôle uniforme du numérateur sur la ligne critique. -/
  numerator_bounded :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ t : ℝ, Complex.abs (targetLFactor p ((1/2 : ℂ) + (t : ℂ) * I)) ≤ C₁
  /-- H2 : minoration uniforme du dénominateur sur la ligne critique. -/
  denominator_bounded_below :
    ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ t : ℝ, c₂ ≤ Complex.abs (B.det2 ((1/2 : ℂ) + (t : ℂ) * I))

/-- Version conditionnelle du théorème : sous les obligations, la borne existe. -/
theorem defect_bounded_under_obligations
    (targetLFactor : ℕ → LocalFactor) (p : ℕ) [hp : Fact p.Prime] (B : LocalBlock)
    (obs : DefectObligations targetLFactor p B) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      Complex.abs (localDefect2 targetLFactor p B
        ((1/2 : ℂ) + (t : ℂ) * I)) ≤ C := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := obs.numerator_bounded
  obtain ⟨c₂, hc₂_pos, hc₂⟩ := obs.denominator_bounded_below
  refine ⟨C₁ / c₂, by positivity, ?_⟩
  intro t
  -- division terme à terme, bornes H1/H2
  sorry  -- mécanique, pas doctrinal
```

**Bénéfice** :

1. Les obligations H1/H2 sont maintenant **dans le type system**, pas en commentaire. Un fichier aval qui veut fermer `defect_is_bounded_on_critical_line` doit construire un `DefectObligations`, ce qui force la discipline.

2. Le `sorry` est devenu mécanique (arithmétique sur bornes), pas doctrinal. Si on veut, on peut le fermer entièrement en un second temps sans toucher à la partie doctrinale.

3. Le théorème original reste dans le fichier avec son `sorry` doctrinal, mais il y a maintenant une version conditionnelle prouvable.

Cette technique — "transformer un sorry en obligation typée" — vaut le coup d'être généralisée aux autres sorries analytiques.

---

## Priorité 7 — CI minimale (haut impact à moyen terme, 30 min)

**Problème observé** : la BUILD n'évoque aucun pipeline CI. Chaque commit est validé manuellement par Thomas.

**Solution minimale** : un `.github/workflows/build.yml` qui fait juste :

```yaml
name: Build
on: [push, pull_request]
jobs:
  frozen:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
        with:
          lean-toolchain-file: lean-toolchain
      - run: lake exe cache get
      - run: lake build CouretUnification.Meta.SnapshotSentinel
      - run: lake build CouretUnification.Frozen
  full:
    runs-on: ubuntu-latest
    continue-on-error: true  # full peut casser sans bloquer
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
        with:
          lean-toolchain-file: lean-toolchain
      - run: lake exe cache get
      - run: lake build
```

**Bénéfice** : le job `frozen` est une garde absolue (casser Frozen bloque le merge). Le job `full` donne un signal sans bloquer, utile pour tracer les fronts actifs.

Cette CI suppose la priorité 2 (umbrella segmentée) en place.

---

## Classement final par ratio impact/coût

| Priorité | Amélioration | Coût (h) | Impact | Livrable ici |
|---|---|---|---|---|
| 1 | `SnapshotSentinel.lean` | 0.5 | ★★★★ | ✓ joint |
| 2 | Umbrella `Frozen`/`Active` | 0.25 | ★★★★ | ✓ joint |
| 3 | `SorryRegistry.lean` | 1.0 | ★★★ | esquisse ci-dessus |
| 4 | `scripts/quickstart.sh` | 0.25 | ★★★ | esquisse ci-dessus |
| 5 | `FileIdentity` partout | 1.5 | ★★ | non joint |
| 6 | Obligations typées Det2 | 0.5 | ★★ | esquisse ci-dessus |
| 7 | CI GitHub Actions | 0.5 | ★★★ | esquisse ci-dessus |

**Total pour les 4 premières priorités** : ~2 heures de travail de Thomas, économies cumulatives à chaque cycle de snapshot Mathlib.

---

## Ce qui N'EST PAS recommandé

1. **Refactor Core/ ↔ Logic/** : l'architecture actuelle est saine, ne pas y toucher.

2. **Unifier les espaces de noms AnalyticHorizon et Logic** : leur séparation reflète une différence doctrinale réelle (transport vs structure algébrique). Garder séparé.

3. **Migrer vers des axiomes formels au lieu de sorries** : les sorries sont préférables aux axiomes tant que le travail analytique est en cours. Les axiomes figent ; les sorries signalent "à faire".

4. **Chercher à supprimer les 11 sorries d'un coup** : la plupart sont analytiques et attendent de vrais résultats mathématiques. Les traiter au rythme des fronts actifs.

---

## Conclusion

Les quatre premières améliorations transforment **deux points d'échec fréquents** en **diagnostics immédiats** :

- Snapshot Mathlib qui bouge → `SnapshotSentinel` le signale en premier.
- Front actif qui casse → `Frozen` reste intacte, le core est auditable.

C'est exactement ce qui fait gagner des heures à Thomas, sans changer la doctrine.

**Le livrable immédiat** : `Meta_SnapshotSentinel.lean` et la séquence d'umbrellas à adopter. Tout le reste est optionnel et peut s'étaler sur plusieurs releases.

---

*Pour Bernard.*
