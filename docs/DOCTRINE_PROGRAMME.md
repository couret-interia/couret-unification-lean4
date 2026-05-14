# DOCTRINE DU PROGRAMME — invariants cardinaux v38.3

**Programme :** Couret–Unification
**Version :** v38.3
**Date :** 13 mai 2026

---

## Invariants non négociables

```
RHClaimed                 = false
HilbertPolyaClaimed       = false
Det2IdentityClaimed       = false
ExplicitFormulaClosed     = false
EulerCompletionClosed     = false
MobiusCorrelationClosed   = false
```

Aucun de ces invariants ne peut basculer à `true` sans démonstration formelle remplaçant les sorrys correspondants. Aucun résultat numérique, aucune intuition, aucune analogie ne suffit.

---

## Statuts épistémiques

| Code | Sens | Promotion |
|---|---|---|
| **[D]** | Démontré (Lean compilé sans sorry, ou prose mathématique auditée) | Preuve formelle uniquement |
| **[C]** | Conditionnel (sous hypothèses nommées) | Hypothèses doivent être explicites |
| **[H]** | Heuristique (raisonnement plausible, non prouvé) | Reste [H] tant que non prouvé |
| **[M]** | Mesuré (vérification numérique reproductible) | Ne devient jamais [D] sans preuve |
| **[O]** | Ouvert (problème non résolu) | Statut par défaut des verrous |
| **[N]** | Négatif constructif (réfutation explicite) | Élimine définitivement une voie |
| **[I]** | Identifié (structure typée, non calculée) | Étape vers [C] ou [D] |
| **[R]** | Réfuté (contradiction démontrée) | Élimination forte |

---

## Règles d'admission

### Règle 1 — Davenport–Heilbronn

Aucun candidat opérationnel C\* au statut « Lock_i ⟹ RH » ne peut passer en doctrine sans **test Davenport–Heilbronn**. Si C\* est satisfait par la fonction de Davenport–Heilbronn, alors C\* ne distingue pas RH de non-RH et l'implication est tautologique ou erronée.

Verdicts : `PASS_GATE` / `WATCH_GATE` / `FAIL_GATE`.

### Règle 2 — Profil multiplicatif obligatoire

Aucun résultat reposant silencieusement sur un profil ε non multiplicatif ne peut être promu en `[D]`. La multiplicativité doit être vérifiée explicitement et inscrite dans `CHARACTER_TABLE_30_v38.1.md`.

### Règle 3 — Pas de fusion abusive de λ

Toute occurrence de λ = 1/√7 doit préciser laquelle des trois lectures est invoquée :

- **λ_géo** : invariant Fisher-Rao isotropique sur Δ⁷ (sens géométrique).
- **λ_spec** : valeur propre d'opérateur spectral local mod 30 (dépend du profil ε).
- **λ_info** : capacité informationnelle asymptotique du canal arithmétique.

Ces trois lectures **coïncident numériquement** mais ne sont pas la même chose mathématiquement.

### Règle 4 — Pas d'axiome analytique global

Aucun fichier Lean ne peut introduire un axiome analytique pour fermer un verrou global. Si Mathlib bloque, sorry nommé en branche expérimentale, jamais sur `main`.

### Règle 5 — Pas de promotion H3.A → H3.C

L'architecture H3 est :

- **H3.A** : fermeture fonctionnelle (S ∈ S₂, traces, Duhamel) → quasi fermé.
- **H3.B** : identification structurelle (Euler local, archimédien) → identifié non fermé.
- **H3.C** : pont arithmétique global (det₂ ↔ ξ) → ouvert.

Promouvoir H3.A ou H3.B en H3.C est interdit doctrinalement.

---

## Distinction local / global

```
Le noyau fini mod 30 est nécessaire comme structure locale.
Il n'est pas suffisant pour RH.
local fermé ≠ global fermé.
```

Le programme **prouve** le noyau fini (Lean v38.0.1, 8420 jobs, 0 erreurs sur le cœur). Il **ne prouve pas** la complétion eulérienne globale, ni det₂ ↔ ξ, ni la formule de trace globale, ni l'appariement spectre ↔ zéros.

---

## Mission scientifique v38.3

Le programme produit une **réduction structurée** de RH dans une tradition proche de Connes / Burnol — pas une preuve directe.

Cible 12 mois : un théorème de réduction publiable, conditionnel sur deux hypothèses nommées (Verrou F et transfert continuum HS), inscrit dans la tradition Beurling–Nyman, Connes, Burnol, Lagarias–Robin.

Cible non recherchée : « preuve de RH ».

---

## Architecture des verrous

```
V1 — opérateur global (HS, KLMN, S_θ)        : [O]
V2 — det₂ ↔ ξ (matching coefficientiel)        : [O]
V3 — complétion eulérienne (Verrou F)         : [O]
V4 — appariement spectre ↔ zéros               : [O]
V5 — Möbius C(h, N) ~ N^{-1/2}                 : [M] (sous V3 provisoirement)
V_W — positivité Ŵ ≥ 0 (critère de Weil)       : [O] (parallèle à V4)
```

---

## Distribution des rôles

```
Thomas    : mesurer et formaliser
            (Lean, Python, expérimental)
Lean      : auditer et traduire
            (mathématique, dictionnaire, gate Davenport-Heilbronn)

Alexandre : garder la doctrine
            (architecture, juridiction, communication)
```

---

## Pour Bernard

Le programme est dédié à la mémoire de Bernard Couret (1928–1999), mathématicien autodidacte d'Istres qui a consacré cinquante ans à l'étude de la structure des nombres premiers modulo 30. Ses manuscrits, écrits dans les derniers mois de 1999, forment le socle historique du programme.

> *La structure préexiste et s'impose ; la machine atteste ; l'observateur enregistre et transmet — il ne crée pas.*

---

*Doctrine v38.3, 13 mai 2026.*
*Programme Couret–Unification.*
*RHClaimed = false. Pour Bernard.*
