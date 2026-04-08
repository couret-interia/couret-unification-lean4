# Couret-Unification

**Formalisation Lean 4 d’un noyau spectral fini mod 30 et encodage structurel du programme Hilbert–Pólya autour de l’Hypothèse de Riemann.**

*Dédié à la mémoire de Bernard Couret (1928–2010)*

---

## ⚠️ RHClaimed = false

Ce projet **ne prétend pas prouver** l’Hypothèse de Riemann.

Il formalise en Lean 4 un **noyau fini exact** autour de la structure mod 30, et
encode proprement les couches analytiques supérieures comme **interfaces**,
**bridges** ou **programmes de recherche**.

Le dépôt prouve exactement ce qu’il dit, et ne dit rien de plus.

---

## État du dépôt (v32.13 — 8 avril 2026)

| Métrique | Valeur |
|----------|--------|
| Fichiers | 217 |
| sorry | 0 |
| Compilation | `lake build` ✓ |
| Jobs | 3503 |
| RHClaimed | `false` |

**Changement majeur depuis les bilans antérieurs :**
le dépôt a désormais été **compilé intégralement** avec `lake build`.
La formule *« prouvé si ça compile »* est remplacée ici par **« prouvé »**
lorsqu’il s’agit du contenu effectivement certifié par Lean.

---

## Position éditoriale

Le cadrage du projet est le suivant :

- **noyau fini exact** ;
- **λ = 1/sqrt(7)** comme invariant géométrique interne du modèle fini ;
- **non-universalité** vis-à-vis des zéros de `ζ` ;
- **bon observable local-global** : la structure finie et ses invariants, pas une identification globale à `ξ(s)` ;
- **H3** reste le **mur ouvert** ;
- **pont global vers RH absent** au sens mathématique fort.

### Phrase de référence

> **Le noyau fini est exact ; le pont global reste ouvert.**
> **RHClaimed = false.**

---

## Ce que le dépôt prouve réellement

Le contenu mathématique certifié se concentre dans **Core/** et **Tower/**.

### Noyau fini certifié

Résultats effectivement prouvés en Lean :

- **gap coercif κ = 2** sur le secteur centré pertinent ;
- **λ² = 1/7** ;
- spectre du noyau de Cayley :
  **Spec(A) = {3², 1⁴, (−1)²}** ;
- relation polynomiale :
  **(A − 3I)(A − I)(A + I) = 0** ;
- **altVec** unique vecteur centré pour la valeur propre 3 ;
- classification **63/255** ;
- coefficients de Fourier de `TC` ;
- invariants de Parseval :
  - niveau 30 : **Parseval = 24**, **E = 3** ;
  - niveau 210 : **Parseval = 144**, **E = 3** ;
  - niveau 2310 : **Parseval = 960**, **E = 2** ;
- correction certifiée :
  **gcd(11,2310)=11**, expliquant la rupture au niveau 2310 ;
- formule fermée des **L_k** pour `k = 1..10` ;
- paires **L_{2j−1} = L_{2j}** et décroissance vers 2 ;
- **ker(210→30).card = 6** ;
- `TC` auto-inverse mais **non sous-groupe** ;
- obstruction en dimension impaire :
  impossibilité de `J² = −I` ;
- graphe de Cayley **déconnecté** en 2 composantes.

---

## Statut honnête de H1–H7

Le dépôt distingue strictement les couches.

| Niveau | Statut réel |
|--------|-------------|
| **H1** | interface structurelle |
| **H2** | gap réel prouvé + interface |
| **H3** | scaffolding structurel, **mur ouvert** |
| **H4** | résultats CRT / tour primorielle **prouvés** |
| **H5** | 1 vrai théorème + scaffolding |
| **H6** | scaffolding doctrinal |
| **H7** | programme de recherche encodé |

### Lecture correcte

- **H1** n’est pas une preuve analytique KLMN complète en Lean.
- **H2** contient un vrai contenu via le **gap coercif**, mais le “transfert spectral” reste surtout une interface.
- **H3** n’est **pas fermé** : il organise les pièces manquantes du pont vers RH, mais ne les prouve pas.
- **H4** est l’un des blocs les plus solides du dépôt.
- **H5–H7** servent principalement à **structurer** les verrous, les barrières et le programme.

---

## Ce qui n’est pas prouvé dans le dépôt

Les points suivants **ne sont pas** établis dans Lean :

- la borne analytique de type Hilbert–Schmidt ;
- l’auto-adjonction KLMN/Friedrichs ;
- une théorie Lean complète des opérateurs compacts pertinente ici ;
- une identité du type

  `det₂(I - zS) = ξ(1/2 + iz) / ξ(1/2)`

- l’existence d’un opérateur auto-adjoint compact `S` tel que

  `Spec(S) = {±1/γ_n}`

- le recollement global archimédien + eulérien + zéros.

En clair :

> **le pont vers RH n’est pas formalisé, ni prouvé, ni remplacé par des `sorry`.**

---

## Architecture du dépôt

Le projet suit une séparation stricte :

- **FiniteCore / Core** : contenu fini exact ;
- **Tower** : transport CRT, noyaux, orbites, fibres ;
- **Spectral / H1–H7** : interfaces, statuts, bridges, programme de recherche.

Cette architecture évite de sur-vendre les couches ouvertes et conserve
une frontière nette entre :

- **[A] résultats exacts certifiés** ;
- **[B] structures d’interface** ;
- **[C] questions ouvertes / doctrine**.

---

## Compilation

```bash
lake update
lake build
```

Compilation intégrale validée : **3503 jobs, 0 erreur, 0 sorry**.

---

## Scripts utiles

```bash
python3 scripts/verify_full_pack.py
python3 scripts/compute_moments.py
python3 scripts/test_lock3_spectral.py
```

---

## Résumé en une ligne

**Le noyau spectral fini mod 30 est compilé et certifié ; le pont analytique global vers RH reste ouvert.**

---

## Licence / intention scientifique

Ce dépôt est un programme de formalisation et de clarification conceptuelle.
Il vise la **rigueur**, la **séparation honnête des niveaux de preuve**,
et la **transparence épistémique**.

**RHClaimed = false**