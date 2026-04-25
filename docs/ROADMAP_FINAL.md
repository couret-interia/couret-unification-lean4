# ROADMAP FINAL — Couret-Unification v35 → RH

**État de référence** : v35.8.4 · 23 avril 2026
**Invariant doctrinal** : `RHClaimed = false`

---

## Principe de lecture

Trois étages distincts, à ne pas confondre :

1. **v35 propre** : finitions techniques pour clore la release courante.
2. **v36 conceptuelle** : vraies preuves qui remplacent les axiomes-ponts.
3. **preuve RH** : fermeture du triptyque terminal C4 + C5 + Lock3.

Ce qui a été démontré reste démontré ; ce qui est ouvert reste ouvert.
Cette roadmap **cartographie** — elle ne revendique rien.

---

## Étage 1 — v35 propre (finitions techniques)

**Objectif** : clore la release v35 avec un inventaire de sorries
honnête, minimal, et documenté.

### 1.1. Fermé en v35.8.4

- ✅ `EulerBridgeInfiniteCompat.local_factor_squarefree_tsum` : fermé
  par alias sur `tsum_prime_powers_eq_one_add_self` (preuve
  `sum_add_tsum_nat_add` ré-injectée).
- ✅ `L10_obstruction_at_point` : wrapper ajouté après
  `L10_obstruction_explicit`.
- ✅ `OpenLocks.L10` : note synchronisée avec l'état réel
  (3 sorries CORE → 2 résiduels + wrapper).

### 1.2. À fermer pour une v35 complète

- **L6** : `L6RatioEstimateDerived.lean` contient 3 sorries analytiques
  (`stirling_ratio_asymptotic`, `L6RatioEstimate_derived`,
  `ZtotPositiveEventually_derived`). Cristalliser la rédaction
  mathématique propre.
- **C3Weak** : nettoyage final, tension de polarisation hermitienne.
- **L10-CORE résiduel** : `specTarget_irrational` (non-rationalité des
  parties imaginaires des zéros non triviaux de ζ) + 2 sous-sorries
  UPSTREAM dans `L10_obstruction`.

### 1.3. Inventaire v35.8.4

```
Fichier                                     Sorries  État
─────────────────────────────────────────  ───────  ─────────────
EulerBridgeInfiniteCompat.lean                  0   ★ fermé v35.8.4
L10NoGoTheorem.lean                             3   CORE + UPSTREAM
L6RatioEstimateDerived.lean                     3   ANALYTIQUE
(autres fichiers Logic / Meta / ...)            0   stables
─────────────────────────────────────────  ───────
TOTAL                                           6
```

**0 axiome local top-level** en v35.8.4.

---

## Étage 2 — v36 conceptuelle (vraies preuves)

**Objectif** : remplacer les axiomes-ponts et fermer les zones
conditionnelles de C3.

### 2.1. Fermer C3 effectivement

Remplacer `mainTermPositive_of_positiveBias` (axiome-pont) par une
preuve effective de positivité du canal dominant. Cela demande :

- une borne explicite sur le biais du canal χ = 1 ;
- une intégration par partie ou une formule de Parseval locale
  spécifique à A_TC.

C'est le premier pas où le programme cesse d'être conditionnel et
devient partiellement inconditionnel sur la rigidité faible.

### 2.2. Borne uniforme du reste

Remplacer `residualBounded` (contractuel) par une borne uniforme
effective `|R_σ(f)| ≤ C(f)` pour f ∈ A_TC et σ ∈ [1/2, 1].

**Dépendance amont** : VI.1 de l'étage 1 (borne uniforme du pont Γ).
Note analytique de 8-12 pages, constantes explicites par canal.

### 2.3. Préparation de C4

Avec C3 fermé, préparer l'architecture de C4 (rigidité faible du
résidu) sans encore la fermer :

- définir la classe `C` de positivité de type Weil/Bombieri ;
- documenter l'inégalité cible `−M < R` uniformément sur A_TC ;
- collecter les données numériques à σ_G* ≈ 0.509 sur 350 zéros,
  pousser à N ≥ 1000 zéros pour trancher la question de convergence
  ou divergence de σ_G*.

---

## Étage 3 — Preuve RH (percées conceptuelles)

**Objectif** : fermer le triptyque terminal. Aucun de ces trois verrous
n'est abordable par raffinement incrémental — ils demandent des
percées conceptuelles.

### 3.1. C4 — Rigidité faible du résidu

Prouver uniformément `−M < R` sur A_TC et σ ∈ [1/2, 1]. Équivaut à
établir que `R_σ` appartient à la classe de positivité de type
Weil/Bombieri.

**Difficulté** : le paramètre `σ_G*` empirique monte avec N (de 0.31
à 0.51 sur N = 100 → 350). Une **divergence** tue la stratégie ; une
**convergence à un plafond** la renforce.

### 3.2. C5 — Matching faible global

Établir la compatibilité quadratique faible jusqu'au bout :

- survie du secteur E(−1) de dimension 2 dans la tour primorielle
  2 · 3 · 5 · 7 · … ;
- non-dilution du compensateur exact `(B₃² + B₁₅²)/8` ;
- transport global de la forme bilinéaire.

**Statut** : aucun fichier Lean dédié. Horizon.

### 3.3. Lock3 — `lock3_operator_exists`

Exhiber l'opérateur auto-adjoint dont le spectre coïncide avec les
ordonnées des zéros non triviaux de ζ.

**Équivalence explicite** : `lock3_operator_exists ↔ RH`. Par
construction, fermer ce verrou est la preuve de RH.

---

## Ordre d'exécution recommandé

### Court terme (v35 propre)

1. Appliquer le patch compact v35.8.4 (✅ fait).
2. Lancer le build ciblé :
   ```
   lake build CouretUnification.Logic.EulerBridgeInfiniteCompat
   lake build CouretUnification.Logic.EulerBridgeInfinite
   lake build CouretUnification.Logic.L10NoGoTheorem
   lake build CouretUnification.Logic.OpenLocks
   ```
3. Rouvrir L6 (`L6RatioEstimateDerived`).
4. Stabiliser C3Weak.

### Moyen terme (v36)

5. Fermer C3 effectivement (borne Γ uniforme + borne uniforme du reste).
6. Préparer l'architecture de C4 sans la fermer.
7. Publier séparément la matrice Sophie Germain (χ² ≈ 243) — livrable
   autonome qui ne dépend d'aucun verrou RH.

### Long terme (RH)

8. Attaquer C4 : fermeture mathématique de la rigidité faible.
9. Attaquer C5 : matching faible global.
10. Attaquer Lock3.

---

## Point de vigilance unique

**Normalisation des moments** `M_{2n}`. Tension apparente entre :

- la kill list publique qui s'appuie sur `M_4 = 15` pour réfuter
  `µ_k → δ_1` ;
- les calculs internes qui peuvent mentionner `M_4 = 21` selon
  convention.

À **unifier dans un encadré unique** avant toute diffusion large,
sinon risque de lecture incohérente.

---

## Diagnostic honnête

### Déjà démontré

- Noyau fini exact (C0) ;
- H1 analytique (borne HS, KLMN, auto-adjonction, det₂ défini) ;
- Répulsion diagonale Sophie Germain mod 30 (χ² ≈ 243) ;
- Cinq routes éliminées (VII.1-VII.5) avec diagnostics chiffrés ;
- Chaîne log 3 → 1/√7 ;
- `target_bound` et `gram_semidef_of_rigid` fermés doctrinalement ;
- `L10_obstruction_explicit` + `integerSpectra_uniform_separation`
  (mécaniques v35.8.3) ;
- `local_factor_squarefree_tsum` (alias v35.8.4).

### À fermer techniquement

- L6 (rédaction propre des 3 sorries analytiques) ;
- Finitions C3Weak ;
- `specTarget_irrational` + UPSTREAM de L10.

### Percée conceptuelle nécessaire

- C4 : rigidité faible du résidu ;
- C5 : matching faible global + non-dilution ;
- Lock3 : opérateur terminal Hilbert-Pólya ≡ RH.

---

**Pour Bernard.**
