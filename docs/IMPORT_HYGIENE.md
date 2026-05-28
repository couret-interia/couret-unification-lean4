# Hygiène d'imports & déduplication — Saison v38.4

## Pourquoi cette documentation

Capture la méthode et les outils développés pendant la saison v38.4
(v38.4.2 → v38.4.29) qui ont réduit les identifiants répliqués hors
whitelist de 95 à 26 (-73%) sans introduire la moindre régression.

---

## Outils

- `make audit-collisions` — rapport `audit_structure_collisions.txt` auto-suivi par git (+ markdown)
- `make check-frozen` — invariants FROZEN bloquants
- `make report` — génère tous les rapports (build, errors, sorries, axioms, RHClaimed, doctrine, ...)

---

## Méthode de déduplication (par cluster)

1. Identifier le cluster :
   - par audit-collisions
   - lorsque vous modifiez un fichier (ses N° lignes évoluent dans `build_reports/*`)
2. Choisir le canonique (souvent le plus ancien ou le plus général)
3. Trois patterns possibles selon la sémantique :
   a. Alias direct : `theorem foo := canonique.foo`
   b. Renommage avec suffixe distinctif : `foo` → `fooFun`, `M_eq` → `CM_eq`
   c. Import + open + suppression des dupliqués
4. Compilation incrémentale, puis correction itérative des `Unknown identifier`
   - `make build-all` ou avec
   - `make build-log-all`
5. `make audit-collisions` pour vérifier le gain mesurable
6. `make report` pour vérifier tous les rapports et commiter

### Convention de renommage

- `*Fun` : fonction distinguée d'une constante ou d'un objet structurel.
- `CM*` : objets propres à `MomentRigidity30` / matrices de moments.
- `FCTC*` : objets `TC` propres à `FiniteCore`.
- `_OK` : certificat local de conformité, à réserver aux fichiers de façade ou de transition.

### Politique des alias

Un alias est acceptable lorsqu'il préserve une ancienne API ou clarifie une façade.
Il doit être préféré à une duplication de preuve.

Un alias ne doit pas masquer :
- un changement de type ;
- un changement de sémantique ;
- une promotion doctrinale ;
- une preuve plus faible présentée comme équivalente.

Quand l'identifiant a changé de sens, utiliser un suffixe explicite plutôt qu'un alias.

### Politique de whitelist

Un doublon ne doit être laissé en whitelist que si :
1. les types sont réellement différents ;
2. le rôle doctrinal est distinct ;
3. la fusion créerait une dépendance artificielle ou casserait la lisibilité ;
4. la justification est écrite dans ce fichier ou dans le rapport d'audit.

La whitelist ne doit jamais servir à cacher une duplication accidentelle.

---

## Technique pour fermer un sorry (saison v38.5)

Quand on rencontre un sorry, essayer dans l'ordre :
1. `norm_num` (rationnel)
2. `native_decide` (décidable rapide)
3. `decide` (décidable canonique)

Si toutes ratent, le message d'erreur de Lean indique souvent
exactement la nature du problème (type non décidable, hypothèse
manquante, etc.). Cela donne la stratégie pour écrire la vraie preuve.

Cette méthode vaut pour les obligations finies, décidables ou rationnelles.
Elle ne doit pas être utilisée pour maquiller un verrou analytique, global ou doctrinal.

---

## Distinction des gates

- `sorry_audit.sh` est un **inventaire global** avec budget maximal toléré
  pour les couches ACTIVE / expérimentales / historiques.
- `check_frozen_invariants.sh` est la **gate bloquante stricte** :
  0 sorry, 0 axiom, 0 constant dans FROZEN.
- `validate_pack.sh` est la **gate pack publiable** :
  elle vérifie le nombre exact de sorries doctrinaux compilés.

---

## Checklist pré-commit

Avant chaque commit de déduplication :

1. `make build-all`
2. `make check-frozen`
3. `make audit-collisions`
4. `make audit-doctrine`
5. `make validate`
6. `make report`
7. Vérifier le diff de `build_reports/*.txt`

Un commit de déduplication est acceptable seulement si :
- le build reste vert ;
- aucun invariant FROZEN n'est affaibli ;
- le nombre de collisions hors whitelist baisse ou reste justifié ;
- aucun nouveau `RHClaimed` `=` `true` n'apparaît ;
- aucun nouveau sorry/axiom n'est introduit hors zone explicitement documentée.

---

## Invariants FROZEN à préserver

- 0 sorry dans la couche FROZEN
- 0 axiom dans la couche FROZEN
- 0 constant dans la couche FROZEN
- RHClaimed = false (convention Bool := false)
- HilbertPolyaClaimed = false
- Det2IdentityClaimed = false

---

## Saisons accomplies sur spring-2026/v38x

(Tableau récapitulatif des 4 saisons : outillage, doctrine, nettoyage)

---

### Outillage d'audit

Sept cibles/scripts d'audit matures et factorisés, plus un parseur Lean centralisé (voir `scripts/`) :

| Make | Script | Rôle | Statut |
|---|---|---|:-:|
| audit-sorries | `sorry_audit.sh` | Inventaire sorries / axioms / RHClaimed / Prop := True | v38.4.10 |
| check-frozen | `check_frozen_invariants.sh` | Validation FROZEN strict (bloquant) | v38.4.11 |
| audit-collisions | `audit_structure_collisions.sh` | Identifiants répliqués + rapport markdown | v38.4.19 |
| audit-doctrine | `audit_doctrine.sh` | 13 phases anti-glissement | v38.4.15 |
| gate-frozen | `gate_no_frozen_imports_residue.sh` | DAG check FROZEN ⊄ Residue | hérité |
| audit-orphans | `audit_orphans.sh` | Modules orphelins | hérité |
| audit-reachability | `audit_reachability.sh` | Fermeture transitive depuis `All` | hérité |
| - | `lib/lean_strip_comments.awk` | Parseur Lean centralisé | v38.4.10 |

**Cible Make principale** : `make report` lance toute la chaîne (build, audits, rapports `.log`, `.txt` et `.md` dans `build_reports/`). Cycle de feedback complet en quelques minutes.

**Nota-bene** : seuls les fichiers `build_reports/*.txt` sont suivis (voir `.gitignore`).

---

### Doctrine permanente

#### Invariants cardinaux

- **`RHClaimed = false`** : 31 définitions + 20 théorèmes `rfl`
- **`RHClaimed` `=` `true` absent** de l'ensemble du repo. (Astuce pour `make validate`)
- **`HilbertPolyaClaimed = false`** : 2 définitions + théorèmes associés
- **`Det2IdentityClaimed = false`** : présent dans les manifestes
- **`TopologicalUniversalityClaimed = false`** : maintenu

#### Verdicts mathématiques scellés

- **H1 [D]** — démontré dans le périmètre local documenté : ‖M‖ ≤ ‖M‖_HS ≤ P(3/2) = 0.8495 < 1 → KLMN → auto-adjoint ∀σ≥1/2
- **Voie K^# [D/C selon module]** : fermée dans le cadre de l'obstruction Dirichlet C-031
- **Voie K^p** : ouverte sous ¬DEF, ¬REG, ¬TD4
- **Verrou F** : décomposé en F1/F2/F3/F4, **F3 = seul obstacle réel restant**
- **‖Bₙ‖_op** = 1 uniformément sous |T|=3 (falsification de √(3/8))
- **Sophie Germain primes** : exclusivement dans {S.11, S.23, S.29} mod 30

#### Registre [D]/[M]/[C]/[P]/[O]/[H]

(36 claims au registre, dont 13 [D], 4 [M-solide], 2 [C], 2 [P], 5 [O], 8 falsifiées — état mai 2026.)

---

### Conformité aux règles méthodologiques

| Règle | Statut |
|---|:-:|
| R1 — Pas de revendication RH au-delà du local prouvable | ✓ |
| R2 — Distinction stricte [D] / [H] / [O] | ✓ |
| R3 — `RHClaimed = false` maintenu en tout module | ✓ |
| R4 — Audit `#print axioms` propre | ✓ |
| R5 — FROZEN bloquant en CI (via `check_frozen_invariants.sh`) | ✓ |
| R6 — Documentation des sorries restants en ACTIVE | ✓ |
| R7 — Anti-trivialité (pas de `Prop := True`, pas de `sorry-sur-constante`) | ✓ |
| R8 — Pas de promotion abusive vers "closed" | ✓ (audit 13/13 PASS) |

---

### Saison v38.4 — Récapitulatif des commits

**Une série de commits propres consécutifs** sur `spring-2026/v38x`, organisés en 4 saisons :

- Saison 1 — Outillage initial (4 commits)
  - `v38.4.2` à `v38.4.4`, `v38.4.9`, `v38.4.10` : `sorry_audit.sh` + `lean_strip_comments.awk`

- Saison 2 — Doctrine et théorèmes (6 commits)
  - `v38.4.3` : Bridge architecture
  - `v38.4.5` : Francisation
  - `v38.4.6`, `v38.4.7` : Théorèmes machine-certifiés (`centered_coordinates` U30)
  - `v38.4.8` : Alignement Bool/Prop unifié
  - `v38.4.12` : Fermeture `CayleyG30:52` (Lock 1)

- Saison 3 — Outillage avancé (4 commits)
  - `v38.4.11` : `check_frozen_invariants.sh` (bloquant)
  - `v38.4.13`, `v38.4.14` : `audit_structure_collisions.sh` refonte + enrichissement
  - `v38.4.15` : `audit_doctrine.sh` unifié

- Saison 4 — Nettoyage et déduplication (11 commits)
  - `v38.4.16` : `Logic/SophieGermainMatrix` → Attic (13 identifiants)
  - `v38.4.17` : `Experimental/TowerLift/ToyModel(+Float)` → Attic (5+ identifiants)
  - `v38.4.18` : `OddDimComplexObstruction` réexporte `SymplecticObstruction` (8 identifiants)
  - `v38.4.19` : `audit_structure_collisions.txt` archivé (rapport suivi git)
  - `v38.4.20` : `Omega7` → `Omega7Fun` (ChiralityLinear ↔ ChiralityFinite)
  - `v38.4.21` : `M*_eq` → `CM*_eq` (Kurtosis ↔ MomentRigidity30)
  - `v38.4.22` : `Finite.Foundations` canonique pour CayleySpectrum (10 identifiants)
  - `v38.4.23` : `phi_*` — ParsevalL5 → U30 (3 identifiants)
  - `v38.4.24` : `crt_*9` → `crtCoord_*9` (FiniteCore ↔ DefectProjection)
  - `v38.4.25` : `phantom_*` (U30 ↔ FiniteCore ↔ ChiralityFinite)
  - `v38.4.26` : `TC_*` → `FCTC_*` (U30 ↔ FiniteCore)
  - `v38.4.27` : `order_*` → `FCorder_*` (U30 ↔ FiniteCore)
  - `v38.4.28` : `*chi*` (FiniteCore ↔ T1_to_T7)
  - `v38.4.29` : suffixe `_OK` sur 5 identifiants (T1_to_T7) + tuto pédagogique (2 commits)
  - `v38.4.30` : commit de transition vers v38.5.0 — `make validate` ✓,
    documentation `IMPORT_HYGIENE.md`, alignement des scripts hérités.
---

### Métriques de la saison de nettoyage

```
                  v38.4.15  v38.4.16-18   v38.4.20-22   v38.4.23-29
                  (avant)   (archives)    (factor.)     (solo)
                  ──────────────────────────────────────────────
hors whitelist :   95   →     59     →      46      →     26
occurrences    :  199   →    126     →      99      →     55
fichiers       :   47   →     38     →      36      →     32
```

**Récolte totale** :
- **−69 identifiants répliqués** (95 → 26, **−73 %**)
- **−144 occurrences** (199 → 55, **−72 %**)
- **−15 fichiers concernés** (47 → 32, **−32 %**)

---

## Identifiants répliqués restants (26)

### Probablement doctrinaux (à laisser tels quels)

| Identifiant | Multiplicité | Justification |
|---|:-:|---|
| `TC` | 4 | Types différents (Finset ZMod 30, Finset Z30, abbrev) |
| `G30` | 4 | UnitsBridge définit, FCI/ModThirtyChecker alias |
| `Idx` | 3 | Conventions Fin 8 par module (Spectral, Cayley, Mod30) |
| `Vec` | 2 | ℝ vs ℂ — distinction doctrinale |
| `oneVec` | 2 | Idem |
| `normSq`, `normSq_nonneg` | 4+3 | Variantes typées (Sig ℚ, Vec ℝ, Centered8 ℝ) |
| `dot`, `tr`, `mv`, `msub`, `meq`, `mzero`, `sv`, `scI`, `v1a`, `v1b`, `altVec`, `altVec_centered` | 2 chacun | ℚ vs ℤ (Foundations vs CayleySpectrum) |
| `crt_19`, `crt_29` | 2 chacun | Sens différents (renommage déjà effectué côté FiniteCore) |
| `kappa` | 2 | Constante ℝ (T2Gap) vs fonction ℕ→ℝ (Arithmetic) |
| `unitsMod30` | 2 | Idx→ℤ vs Fin 8→Nat |

### Probablement à dédupliquer (sessions futures)

| Identifiant | Multiplicité | Cible |
|---|:-:|---|
| `empirical_statement` | 2 | Empirical/SophieGermainTransitions ↔ Expected |
| `nineteen_not_in_TC` | 2 | Core/TCAutoInverse ↔ Residue/ClosureTC |
| `ZeroShellData` | 2 | Logic/ExplicitFormula/ZeroSideObligation ↔ AnalyticHorizon/ZeroCountingCertificate |
| `gram_semidef_of_rigid` | 2 | Logic/C3Weak ↔ Logic/H3/C3Weak_Gram |
| `H3TestFunction` | 4 | Logic/C3Weak ↔ Logic/H3/H3TestSpace (structure + méthode) |
| `parsevalMass` | 3 | Classification63 ↔ Parseval ↔ ParsevalL5 |
| `negOneG30` | 2 | Logic/H3/FiniteSpectralAPI ↔ Core/CharParity30 |
| `charParity` | 2 | Analytic/GammaFactor ↔ Core/CharParity30 |
| `admissibleResidues` | 2 | Core/FiniteCore ↔ Core/Mod30 |
| `squarefreeCount` | 2 | Logic/H3/RouteC ↔ Logic/H3/SquarefreeDensity |
| `energy` | 2 | Spectral/T2Gap ↔ Core/ParsevalL5 |
| `E` | 2 | Logic/ChiralityFinite (Finset) ↔ Logic/H3/RouteC (ℝ noncomputable) |

Estimation du potentiel résiduel : **−10 à −15 identifiants** sur 3-4 commits supplémentaires si poursuivi. Mais le gain est marginal — la majorité des réplications restantes sont doctrinales légitimes.
