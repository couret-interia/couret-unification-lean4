# Meta

Le dossier `Meta/` contient les **métadonnées déclaratives** du projet, et non le noyau mathématique prouvé.

On y place notamment :

- les données empiriques ;
- les constantes expérimentales ;
- les observations numériques ;
- les informations de reproductibilité ;
- les manifestes d’état du dépôt ;
- les éléments d’audit structurel.

## Règle de séparation

Le contenu de `Meta/` ne doit pas être confondu avec :

- les théorèmes substantifs du `Core/` ;
- les preuves effectives du noyau fini ;
- les ponts analytiques encore ouverts du `Bridge/`.

Autrement dit :

- `Core/` = résultats finis exacts et compilés ;
- `Bridge/` = extensions, interfaces, et couches analytiques ;
- `Meta/` = description, traçabilité, audit, reproductibilité, empirique.

## Discipline

Les fichiers de `Meta/` doivent rester :

- honnêtes ;
- explicitement déclaratifs ;
- sans sur-vendre leur portée mathématique.

Quand une donnée n’est pas encore auditée automatiquement, elle doit être :

- soit omise ;
- soit marquée comme provisoire ;
- soit encodée comme inconnue.

## Statut actuel

À ce stade :

- le noyau fini compile ;
- `Meta/` compile ;
- la reproductibilité locale est alignée sur Lean `4.29.0` ;
- aucune revendication analytique supplémentaire n’est introduite par `Meta/`.