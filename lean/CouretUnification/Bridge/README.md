# Bridge

Le dossier `Bridge/` ne contient pas de fermeture analytique globale prouvée.
Il formalise un **programme structuré** au-dessus du noyau fini `Core/`.

## Fichiers

- `Bridge/Status.lean`
- `Bridge/Claims.lean`
- `Bridge/AnalyticChain.lean`
- `Bridge/ContinuousModel.lean`
- `Bridge/CharacterTower.lean`
- `Bridge/Unification.lean`
- `Bridge/VoroninInterface.lean`

## Convention de statuts

```lean
inductive ClaimStatus
  | formalized
  | constructed
  | conditional
  | open_
  | roadmap
  | program
```

## Sens des statuts

- `formalized` : contenu prouvé ou certifié en Lean
- `constructed` : objet défini proprement, sans fermeture analytique globale
- `conditional` : dépend d’hypothèses supplémentaires non fermées
- `open_` : verrou mathématique réellement ouvert
- `roadmap` : étape planifiée du programme
- `program` : interface ou couche de recherche explicitement non theorem-level

## Doctrine

Le dépôt sépare strictement :

- le **Core** : noyau fini formalisé
- le **Bridge** : programme analytique structuré, sans revendication abusive
- les interfaces futures éventuelles : extensions non intégrées au noyau prouvé

## Énoncé correct

Le noyau fini mod 30 est formalisé en Lean.
Le dossier `Bridge/` organise les étapes analytiques et conceptuelles restantes,
sans prétendre fournir une preuve de RH ni une fermeture complète du pont arithmético-analytique.