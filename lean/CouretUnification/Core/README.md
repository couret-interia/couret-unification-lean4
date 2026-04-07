# Core

Le dossier `Core/` contient le **noyau fini exact** du projet.

Ici, la règle est simple :

- pas de faux “proved” ;
- pas de `Prop := True` pour simuler une preuve ;
- pas de `sorry` ;
- seulement des définitions, lemmes et théorèmes réellement établis et compilés.

## Rôle du dossier

`Core/` porte les objets finis, explicites et contrôlés, au niveau du modèle mod 30.

On y trouve notamment :

- l’opérateur fini exact associé au triplet distingué ;
- les profils spectraux gelés (trié / historique) ;
- la masse de Parseval finie ;
- les 21 triplets exacts centrés sur l’identité ;
- l’ordre documentaire des 8 caractères ;
- la couche Fourier minimale sur le noyau fini ;
- le recollement harmonique du triplet distingué avec son spectre documentaire ;
- les invariants finis de transport déjà stabilisés ;
- les restrictions modulaires élémentaires utilisées par le noyau.

## Discipline

Le dossier `Core/` ne doit contenir que des résultats :

- finis ;
- exacts ;
- compilés ;
- explicitement justifiés.

En particulier, `Core/` ne doit pas contenir :

- de pont analytique non fermé ;
- de revendication Hilbert–Pólya globale ;
- d’identification non démontrée avec la théorie complète de `ζ` ;
- de placeholders logiques.

## Ce qui est actuellement stabilisé

À ce stade, `Core/` contient en particulier :

- le spectre documentaire du triplet distingué ;
- le profil quadratique historique ;
- la masse de Parseval `= 24` ;
- l’invariant `E(q)` dans la couche actuellement gelée ;
- la compatibilité CRT déjà formalisée dans le noyau ;
- la restriction Sophie Germain mod 30 ;
- le recollement harmonique explicite du cas Couret.

## Ce qui n’est pas encore revendiqué ici

Le dossier `Core/` ne prétend pas encore :

- classer harmoniquement tous les triplets ;
- fermer une DFT générale au-delà de la couche minimale gelée ;
- établir à lui seul le pont analytique global ;
- démontrer RH, ni une version complète de Hilbert–Pólya.

Ces étapes, lorsqu’elles existent, doivent apparaître ailleurs avec leur statut exact.

## Résumé structurel

- `Core/` = noyau fini exact ;
- `Bridge/` = extensions, transports, couches analytiques ou intermédiaires ;
- `Meta/` = audit, empirique, reproductibilité, manifestes.