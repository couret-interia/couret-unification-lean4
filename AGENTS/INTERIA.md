# Protocole InterIA — Couret-Unification Lean 4

> **Instruction de langue**  
> Répondre en français par défaut. Garder les noms Lean, chemins, commandes, identifiants et messages d'erreur inchangés. Ajouter un court abstract anglais seulement si utile à des contributeurs internationaux.

Ce document est la source canonique pour les agents IA travaillant sur `couret-interia/couret-unification-lean4`.

## Identité

- Organisation GitHub : `couret-interia`.
- Dépôt : `couret-unification-lean4`.
- Namespace Lean : `CouretUnification`.
- Toolchain : Lean `v4.29.1`.
- Mathlib : `v4.29.1`.
- Langue humaine par défaut : français.

## Hiérarchie de confiance

```text
Thomas / compilateur > CI Lean > logs build_reports > assistant IA > interprétation philosophique
```

Un assistant IA peut proposer, relire, déplacer, commenter, documenter. Il ne décide pas seul du statut mathématique final.

## Non-négociable

Ne jamais promouvoir un énoncé au-delà de ce qui est effectivement vérifié.

En particulier, un certificat fini modulo 30 ne prouve pas :

- l'infinité des nombres premiers jumeaux ;
- l'infinité des nombres premiers de Sophie Germain ;
- l'Hypothèse de Riemann ;
- une loi globale de distribution des nombres premiers ;
- un transport automatique du spectral fini vers le comptage premier.

## Statuts autorisés

Voir `STATUS_TAGS.md`.

Tags usuels :

- `[L-verified]`
- `[D-computational, finite]`
- `[T-theorem]`
- `[S-speculative]`
- `[X-blocked]`

## Conventions Lean

Préserver le namespace :

```lean
namespace CouretUnification
namespace Core
-- ...
end Core
end CouretUnification
```

Ne pas introduire dans les fichiers de production :

- `sorry` ;
- `axiom` ;
- `admit` ;
- commentaires revendiquant une conséquence globale non prouvée.

Pour les calculs finis, préférer des définitions explicites et `native_decide` quand l'énoncé est réellement fini et décidable.

## Commandes de référence

Voir `LEAN_AUDIT.md` et `MAKE_TARGETS.md`.

Commandes minimales :

```bash
make build-log-all
make audit-sorries
make audit-warnings
make doctrine-check
```

Avant tag ou release :

```bash
make audit-all
make report
make snapshot
```

## Trois lignes sémantiques

Pour une avancée mathématique importante, ajouter si utile :

1. Ce que la forme montre.
2. Ce qu'elle ne doit pas surdire.
3. Hypothèse philosophique possible, retranchable sans modifier la ligne 1.

La ligne 3 doit rester supprimable sans affecter la validité de la ligne 1.

## Rapport final demandé aux agents

À la fin d'une modification, indiquer :

- fichiers modifiés ;
- commandes lancées ;
- résultat du build ;
- rapports consultés dans `build_reports/` ;
- statut final ;
- risques ou blocages restants.
