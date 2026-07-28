# Checklist PR — Couret-Unification Lean 4

## Résumé

- [ ] Le changement est décrit en français.
- [ ] Un court abstract anglais est ajouté seulement si utile.
- [ ] Les fichiers modifiés sont listés.

## Lean

- [ ] `make build-log-all` lancé.
- [ ] `make audit-sorries` lancé.
- [ ] `make audit-warnings` lancé.
- [ ] `make doctrine-check` lancé.
- [ ] Les rapports `build_reports/` pertinents sont mentionnés.

## Statut

- [ ] Le tag de statut est explicite.
- [ ] Aucun résultat fini n'est surdéclaré en résultat global.
- [ ] Aucun `sorry`, `axiom` ou `admit` nouveau n'est introduit sans justification.

## Doctrine InterIA

- [ ] `RHClaimed = false` reste intact.
- [ ] `HilbertPolyaClaimed = false` reste intact.
- [ ] `Det2IdentityClaimed = false` reste intact.
- [ ] Les interprétations philosophiques restent séparées des énoncés Lean.

## Trois lignes sémantiques, si nécessaire

1. Ce que la forme montre :
2. Ce qu'elle ne doit pas surdire :
3. Hypothèse philosophique possible, retranchable :
