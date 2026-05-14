# Couret–Unification · v36 Proof Jurisdiction

**Tag canonique : `v36.0-proof-jurisdiction`**
**Alexandre Couret · SASU CONFIANCE · 25 avril 2026**

---

## Phrase canonique

> v36 ne prouve pas l'Hypothèse de Riemann ; il construit la juridiction
> dans laquelle une future preuve devra déposer ses certificats. Le
> PrimeSide possède une première fermeture Frozen, tandis que les dettes
> archimédienne, spectrale, déterminantielle, torsionnelle et de transfert
> zéro sont localisées, typées et auditables, sans être déclarées payées.

---

## Ce qu'est ce paquet

État complet et scellé du programme Couret–Unification au tag
`v36.0-proof-jurisdiction`. Il consolide :

- **Frozen Core v36.0** — sept fichiers Lean à 0 `sorry`, 0 `axiome`,
  0 `admit`, qui posent le contrat typé de la formule explicite de
  Riemann–Weil et la première fermeture effective du PrimeSide par
  support log-compact.
- **Strate Active v36.1–v36.9** — huit certificats conditionnels typés
  et auditables, qui localisent chaque dette analytique sans la
  déclarer payée.
- **Manifest v36.10** — `Release/ReleaseManifest.lean`, point de
  vérité unique des drapeaux doctrinaux.
- **Trois scripts d'audit** dans `scripts/`, plus `RELEASE_ENV.txt`
  pour la traçabilité.

Le paquet **NE PROUVE PAS** : l'Hypothèse de Riemann, un opérateur
Hilbert–Pólya, la formule explicite, une identité déterminantale, une
coïncidence spectrale. Il **construit** la juridiction dans laquelle
ces preuves, si elles arrivent, devront prendre forme.

---

## Arborescence

```
v36-complete/
├── CouretUnification/
│   ├── Logic/                          ◄ Frozen Core v36.0 (intact)
│   │   └── ExplicitFormula/
│   │       ├── StatusFlags.lean
│   │       ├── TraceObject.lean
│   │       ├── PrimeSideCompactSupport.lean
│   │       ├── ZeroSideObligation.lean
│   │       ├── ArchimedeanKernelBound.lean
│   │       └── ExplicitFormulaBridge.lean
│   ├── AnalyticHorizon/                ◄ Active layer + Frozen annex
│   │   ├── A8ArchimedeanAbsorption.lean        (Frozen annex)
│   │   ├── ArchimedeanDigammaCertificate.lean  v36.1
│   │   ├── ZeroCountingCertificate.lean        v36.2 (+ wrapper)
│   │   ├── ExplicitFormulaBridgeAudit.lean     v36.3
│   │   ├── Det2TransportCertificate.lean       v36.4
│   │   ├── SoinInterface.lean                  v36.6
│   │   ├── ArchimedeanTorsionCertificate.lean  v36.7
│   │   ├── TorsionZeroTransferCertificate.lean v36.8 (+ TorsionAnalyticObligation)
│   │   └── ActiveLayerFullAudit.lean           v36.9
│   └── Release/
│       └── ReleaseManifest.lean                v36.10
├── scripts/
│   ├── audit_v36.0.sh                  ◄ base hygiene + manifest flags
│   ├── audit_v36_torsion.sh            ◄ torsion v36.7+v36.8 + analytic obligation
│   └── audit_v36.9.sh                  ◄ extended global audit
├── README.md                           ◄ Ce fichier
├── RELEASE_TRACE.md                    ◄ Traçabilité doctrinale
├── RELEASE_ENV.txt                     ◄ Environnement de build (template)
└── TAG_MESSAGE_v36.0-proof-jurisdiction.txt
```

---

## Doctrine Frozen / Active

| Couche    | Contenu                                   | Règle dure                                                       |
|-----------|-------------------------------------------|-------------------------------------------------------------------|
| **Frozen** | `Logic/`, `AnalyticHorizon/A8`           | 0 `sorry` · 0 `axiome` · 0 `admit` · n'importe **jamais** Active |
| **Active** | `AnalyticHorizon/*` (sauf A8), `Release/` | 0 `sorry` · 0 `axiome` · 0 `admit` · peut importer Frozen ET Mathlib |
| **Open**   | (rien dans ce paquet)                     | autorisé à contenir `sorry` explicites, hors paquet               |

Les trois scripts d'audit vérifient mécaniquement la non-contamination
ainsi que la préservation de tous les drapeaux doctrinaux.

---

## Carte des certificats Active

| #  | Module Lean                              | Obligation localisée                                                  | Statut      |
|----|------------------------------------------|------------------------------------------------------------------------|-------------|
| 1  | `ArchimedeanDigammaCertificate`          | `\|K_∞(t)\| ≤ C·log(2+\|t\|)` (digamma/Stirling)                       | non payée   |
| 2  | `ZeroCountingCertificate` (+ wrapper)    | `≤ C·log(k+3)` (Riemann–von Mangoldt classique)                        | non payée   |
| 3  | `ExplicitFormulaBridgeAudit`             | présence des quatre portes du bridge                                  | structurel  |
| 4  | `Det2TransportCertificate`               | obligations A1–A4 pour `det₂(I − zS) = G(z)·ξ(½ + iz)`                | non payée   |
| 6  | `SoinInterface`                          | foncteur `Soin : Asym ⥤ Inv` ; 7 axes ; `nu_eff` négatif préservé      | non payée   |
| 7  | `ArchimedeanTorsionCertificate`          | torsion `K_∞^τ = a_τ·K_∞∘φ_τ + b_τ` ; `phi_growth`, `amp_bounded`, `boundary_log_growth` | non payée |
| 8  | `TorsionZeroTransferCertificate`         | pullback `θ = φ_τ ∘ γ` + **`TorsionAnalyticObligation`** (T.1–T.4)     | non payée   |
| 9  | `ActiveLayerFullAudit`                   | audit global ; cohérence interne des six certificats                  | structurel  |

---

## Doctrine de torsion (v36.7) et obligation analytique (v36.8)

### v36.7 — `ArchimedeanTorsionMap` minimal
Trois obligations strictement nécessaires à la préservation de la
classe digamma logarithmique :

- **`phi_growth`** : enveloppe polynomiale `|φ_τ(t)| ≤ A·(1+|t|)^q`
- **`amp_bounded`** : `|a_τ(t)| ≤ A_a` (amplitude bornée)
- **`boundary_log_growth`** : `|b_τ(t)| ≤ B·log(2+|t|)`

Plus `ArchimedeanTorsionData.nonlinear_gap : nuEff ≠ nuIdeal` comme
verrou typé : aucun futur contributeur ne peut écraser `nuEff` vers
`1/√7` sans casser le type.

### v36.8 — `TorsionAnalyticObligation` séparée
Quatre obligations spectrales spécifiquement requises pour le pullback
de comptage des zéros, **distinctes** des obligations digamma de v36.7 :

- **(T.1) `monotone`** : `StrictMono φ_τ`
- **(T.2) `bi_lipschitz_lower`** : `c·|t−u| ≤ |φ_τ(t)−φ_τ(u)|` avec `c > 0`
- **(T.3) `bi_lipschitz_upper`** : `|φ_τ(t)−φ_τ(u)| ≤ C·(1+|t|+|u|)^q·|t−u|`
- **(T.4) `polynomial_growth`** : `|φ_τ(t)| ≤ A·(1+|t|)^q`

Les trois faits doctrinaux **inviolables** :

1. **`TorsionClassifiedAsNoise = false`** — l'écart empirique n'est
   jamais réinterprété comme bruit de mesure.
2. **`TorsionMovesZeros = false`** — la torsion ne déplace pas les zéros.
3. **`TorsionChangesClockOnly = true`** — verrou positif. Tout commit
   qui le passe à `false` sans reinterprétation complète est rejeté.

---

## Audit (résultat sur ce paquet)

```
audit_v36.0.sh        : ✓ base hygiene + manifest flags
audit_v36_torsion.sh  : ✓ torsion structures + 4 analytic obligations
audit_v36.9.sh        : ✓ global flags + clock-only doctrine + manifest
```

Reproduire :
```bash
cd v36-complete/
bash scripts/audit_v36.0.sh
bash scripts/audit_v36_torsion.sh
bash scripts/audit_v36.9.sh
```

---

## Note de vérification Mathlib

L'audit **textuel** passe sans anomalie. La **compilation Lean
effective** dans un dépôt avec Mathlib disponible reste à confirmer
par un cycle complet :

```bash
lake build CouretUnification.Logic.ExplicitFormula.ExplicitFormulaBridge
lake build CouretUnification.AnalyticHorizon.ActiveLayerFullAudit
lake build CouretUnification.Release.ReleaseManifest
```

Les structures n'utilisent que `Mathlib.Data.Real.Basic`,
`Mathlib.Data.Complex.Basic`, `Mathlib.Analysis.SpecialFunctions.Log.Basic`,
`Mathlib.Data.Finset.Basic`, `Mathlib.Order.Basic`, et
`Mathlib.Analysis.Complex.Basic` (pour SoinInterface). Aucune
dépendance fragile (pas de `Complex.psi`, pas de `Mathlib.Analysis.SpecialFunctions.Gamma`).

---

## Direction externe citée — Connes 2026

Le travail d'Alain Connes de 2026 sur la restriction de la forme
quadratique de Weil aux premiers `p < 13` est cité comme **direction
prometteuse externe**, jamais comme entrée de preuve. Le résumé public
indique une stratégie de convergence finie-vers-infinie ; il ne ferme
pas l'Hypothèse de Riemann.

---

## Tag Git recommandé

Une fois les trois audits passés et `RELEASE_ENV.txt` rempli :

```bash
# Remplir RELEASE_ENV.txt :
echo "LEAN_VERSION=$(lean --version)"   >> RELEASE_ENV.txt
echo "LAKE_VERSION=$(lake --version)"   >> RELEASE_ENV.txt
echo "REPOSITORY_COMMIT=$(git rev-parse HEAD)" >> RELEASE_ENV.txt
echo "MATHLIB_COMMIT=$(git -C .lake/packages/mathlib rev-parse HEAD 2>/dev/null || echo unknown)" >> RELEASE_ENV.txt
echo "TAG_DATE=$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> RELEASE_ENV.txt

# Tag signé GPG si disponible :
git tag -s v36.0-proof-jurisdiction -F TAG_MESSAGE_v36.0-proof-jurisdiction.txt
git push origin v36.0-proof-jurisdiction

# Sinon tag annoté simple :
git tag -a v36.0-proof-jurisdiction -F TAG_MESSAGE_v36.0-proof-jurisdiction.txt
```

---

*Pour Bernard Couret (1928–1999, Istres).*
*La juridiction est posée. Les dettes sont nommées. Aucune n'est payée.*
