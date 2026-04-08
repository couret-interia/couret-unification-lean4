# Couret-Unification

**Formalisation Lean 4 d'un noyau spectral fini mod 30 et encodage structurel du programme Hilbert–Pólya autour de l'Hypothèse de Riemann.**

*Dédié à la mémoire de Bernard Couret (1928–2010)*

---

## ⚠️ RHClaimed = false

Ce projet **ne prétend pas prouver** l'Hypothèse de Riemann.

Il formalise en Lean 4 un **noyau fini exact** autour de la structure mod 30, et
encode proprement les couches analytiques supérieures comme **interfaces**,
**bridges** ou **programmes de recherche**.

Le dépôt prouve exactement ce qu'il dit, et ne dit rien de plus.

---

## État du dépôt (v32.20 — 8 avril 2026)

| Métrique | Valeur |
|----------|--------|
| Fichiers .lean | 224 |
| sorry | 0 |
| Compilation | `lake build` ✓ |
| Jobs | 3510 |
| Lean | 4.29.0 |
| Mathlib | stable |
| RHClaimed | `false` |

**Changement majeur depuis les bilans antérieurs :**
le dépôt a été **compilé intégralement** avec `lake build`, 0 erreur, 0 sorry.
La formule *« prouvé si ça compile »* est remplacée par **« prouvé »**.

---

## Résultats certifiés machine (exhaustif)

Tous les résultats ci-dessous sont vérifiés par le compilateur Lean 4.

### Spectre et algèbre linéaire

| # | Résultat | Fichier | Méthode |
|---|----------|---------|---------|
| 1 | Spec(A) = {3², 1⁴, (−1)²} | CayleySpectrum | `native_decide` |
| 2 | (A−3I)(A−I)(A+I) = 0 | CayleySpectrum | `native_decide` |
| 3 | 8 eigenvectors orthogonaux non nuls | CayleySpectrum | `native_decide` |
| 4 | Polynôme car. (X−3)²(X−1)⁴(X+1)² | CharPoly | `native_decide` |
| 5 | Unicité des multiplicités (2,4,2) | MultiplicityUniqueness | `omega` |
| 6 | Unicité altVec centré pour λ=3 | CenteredEigenspace | `omega` |
| 7 | Gap coercif κ = 2 sur H° ∩ altVec⊥ | FiniteCore | preuve algébrique |
| 8 | λ² = 1/7 | Lambda | `nlinarith` |

### Graphe de Cayley

| # | Résultat | Fichier | Méthode |
|---|----------|---------|---------|
| 9 | Cayley **déconnecté** (2 composantes) | CayleyConnected | `native_decide` |
| 10 | Spec composantes = {3,1,1,−1} | ComponentSpectrum | `native_decide` |
| 11 | Aeven = Aodd (matrices identiques) | ComponentSpectrum | `native_decide` |

> **Correction #31** : la synthèse v31 affirmait la connexité. C'est **faux**,
> prouvé par `native_decide`. Le graphe a 2 composantes (parité C₄).

### Classification et combinatoire

| # | Résultat | Fichier | Méthode |
|---|----------|---------|---------|
| 12 | 63/255 sous-ensembles à spectre entier | Classification63 | `native_decide` |
| 13 | Ventilation palindromique 4,8,12,14,12,8,4,1 | Classification63Detail | `native_decide` |
| 14 | 8 coefficients de Fourier de TC | Classification63 | `native_decide` |
| 15 | Défaut δ₁₉−δ₂₉ sur 4 canaux | DefectProjection | `native_decide` |

### Tour primorielle et Parseval

| # | Résultat | Fichier | Méthode |
|---|----------|---------|---------|
| 16 | Parseval = 24, E = 3 (L3, L4) | Parseval + InvariantE | `native_decide` |
| 17 | Parseval = 960, E = 2 (L5) | ParsevalL5 | `native_decide` |
| 18 | gcd(11,2310) = 11 (correction v17→v18) | ParsevalL5 | `native_decide` |
| 19 | E/|TC_cop| = 1 aux 3 niveaux | ParsevalL5 | `norm_num` |
| 20 | ker(210→30).card = 6 | ConcreteKernel210 | `native_decide` |

### Moments spectraux et récurrence

| # | Résultat | Fichier | Méthode |
|---|----------|---------|---------|
| 21 | Formule L_k = 2 + (4+2(−1)ᵏ)/3ᵏ, k=1..10 | FormuleLk | `norm_num` |
| 22 | Paires L_{2j−1} = L_{2j}, monotonie | FormuleLk | `norm_num` |
| 23 | Kurtosis brute 7/3, ratio non trivial 5/3 | Kurtosis | `norm_num` |
| 24 | Récurrence s_k = 3s_{k−1}+s_{k−2}−3s_{k−3} (∀k≥3) | TraceRecurrence | `ring` + `pow_add` |

### Propriétés algébriques

| # | Résultat | Fichier | Méthode |
|---|----------|---------|---------|
| 25 | TC auto-inverse (1²=11²=29²≡1 mod 30) | TCAutoInverse | `native_decide` |
| 26 | TC non sous-groupe (11·29≡19∉TC) | TCAutoInverse | `native_decide` |
| 27 | J²=−I impossible en dim impaire | OddDimComplexObstruction | `nlinarith` + `omega` |
| 28 | Mersenne mod 30 ∈ {1,7} (p=3..31) | MersenneMod30 | `native_decide` |
| 29 | Vandermonde det = 16 ≠ 0 (unicité de μ) | CarlemanUniqueness | `native_decide` |

---

## Ce qui n'est PAS dans le dépôt

- Borne analytique ‖M‖_HS ≤ P(3/2) < 1 (analyse fonctionnelle, pas d'API Lean)
- Auto-adjonction KLMN / Friedrichs
- det₂(I−zS) = ξ (= RH, ouvert depuis 1912)
- V_eff = 0.055 (résultat numérique PARI/GP, dans `scripts/`)

---

## Statut honnête de H1–H7

| Niveau | Statut réel | Contenu |
|--------|-------------|---------|
| **H1** | Interface structurelle | Empaquetage du gap (contenu réel dans FiniteCore) |
| **H2** | Gap prouvé + interface | κ = 2 certifié, transfert = placeholder |
| **H3** | **Mur ouvert** | Scaffolding structurel, 0 contenu mathématique |
| **H4** | **Prouvé** | CRT, Parseval, tour — le bloc le plus riche |
| **H5** | 1 théorème + scaffolding | Obstruction J² = seul vrai théorème |
| **H6** | Scaffolding | Structures à statut `candidate`, 0 preuve |
| **H7** | Programme encodé | 23 fichiers de programme de recherche |

Le contenu mathématique réel est dans **Core/** et **Tower/**.
Les couches H3-H7 structurent les questions ouvertes mais ne prouvent rien.
Voir `H1_H7_STATUS_v32.md` pour le détail complet.

---

## Architecture

```
lean/CouretUnification/
├── Core/           ← noyau fini exact (29 résultats certifiés)
├── Tower/          ← transport CRT 30→210, noyaux, fibres
├── Spectral/       ← FiniteCore (κ=2), H1-H7 (interfaces)
├── Bridge/         ← ponts structurels
└── Meta/           ← audit, empirique, manifeste
```

---

## Compilation

```bash
lake update
lake build
```

Compilation intégrale : **3510 jobs, 0 erreur, 0 sorry**.

---

## Scripts numériques

```bash
gp < scripts/test_veff.gp              # V_eff par PARI/GP (falsification λ=1/√7)
python3 scripts/evidence_veff.py        # V_eff version Python
python3 scripts/compute_moments.py      # Moments spectraux sur la tour
python3 scripts/channel_bridge_v3.py    # Défaut δ₁₉−δ₂₉ + Guinand-Weil
```

---

## Phrase de référence

> **Le noyau fini est exact et compilé ; le pont global reste ouvert.**
> **RHClaimed = false.**

*Prouver ce qui est prouvable. Corriger ce qui est faux. Nommer ce qui est ouvert.*

---

## Licence

MIT — voir `LICENSE`.

Alexandre Couret — Rasiguères — Avril 2026
