# Check-list des difficultés

Voici une **check-list des difficultés** pour les 11 `sorry`, classée par nature du problème et par ordre de fermeture raisonnable.

## Vue d’ensemble

| Bloc                     | Nombre | Difficulté       | Nature                                         |
| ------------------------ | -----: | ---------------- | ---------------------------------------------- |
| `L10NoGoTheorem`         |      3 | 🟡 moyenne       | preuve technique de séparation / irrationalité |
| `RouteC`                 |      1 | 🟠 élevée        | borne arithmético-analytique active            |
| `L6RatioEstimateDerived` |      1 | 🟠 élevée        | asymptotique / ratio / Stirling                |
| `GammaFactor`            |      4 | 🔴 lourde        | facteur archimédien, équations fonctionnelles  |
| `Det2Transport`          |      1 | 🔴 très lourde   | transport spectral global conditionnel         |
| `Lemma7Residual`         |      1 | ⚫ verrou central | résidu ligne critique / passage global         |

---

# 1. `Logic/L10NoGoTheorem.lean` — 3 `sorry`

## Difficulté probable

🟡 **Fermable en premier**, mais à auditer ligne par ligne.

## Nature

No-go L10 : séparation entre une cible spectrale irrationnelle et des spectres entiers ou discrets.

## Check-list

| Question                                                          | Test                                            |
| ----------------------------------------------------------------- | ----------------------------------------------- |
| L’énoncé est-il purement réel / arithmétique ?                    | Oui probablement                                |
| Utilise-t-il une irrationalité déjà disponible ?                  | vérifier `Irrational`, `Int.fract`, `Real.sqrt` |
| La preuve dépend-elle d’un lemme standard absent ?                | probablement                                    |
| Peut-on isoler les sous-lemmes ?                                  | oui                                             |
| Peut-on fermer par `linarith`, `nlinarith`, `norm_num`, `omega` ? | peut-être partiellement                         |
| Y a-t-il un risque de surclaim ?                                  | faible si l’énoncé est local                    |

## Points sensibles

Les lignes concernées sont :

```text
Logic/L10NoGoTheorem.lean:69
Logic/L10NoGoTheorem.lean:239
Logic/L10NoGoTheorem.lean:245
```

À vérifier :

```text
- nature exacte de `specTarget_irrational`
- dépendance à `Irrational`
- usage de `Int.fract`
- preuve de séparation uniforme
- absence de passage global implicite
```

## Stratégie

Commencer par le premier `sorry`, probablement le plus basique :

```text
specTarget_irrational
```

Puis reconstruire les deux derniers à partir des lemmes intermédiaires.

## Statut visé

```text
[O technique] → [D local]
```

---

# 2. `Logic/H3/RouteC.lean` — 1 `sorry`

## Difficulté probable

🟠 **Élevée**, mais peut-être fermable si le `sorry` restant est local.

## Nature

Route C : contrôle d’erreur / raffinement arithmético-analytique.

## Check-list

| Question                                                          | Test                         |
| ----------------------------------------------------------------- | ---------------------------- |
| Le `sorry` dépend-il de squarefree C-04a/C-04b désormais fermés ? | à vérifier                   |
| Peut-il être remplacé par un lemme C-04a déjà prouvé ?            | possible                     |
| Est-il purement arithmétique ?                                    | probablement pas entièrement |
| Est-il utilisé dans un théorème global ?                          | oui, route active            |
| Peut-il être isolé en bridge conditionnel ?                       | oui si trop lourd            |
| Sa fermeture changerait-elle le statut global ?                   | non, sauf s’il touche F3     |

## Points sensibles

Ligne concernée :

```text
Logic/H3/RouteC.lean:780
```

Vérifier si le `sorry` porte sur :

```text
- `routeC_error_control`
- contrôle de `Σ |E_d|`
- passage squarefree → S1
- borne sur `kappa`
```

## Stratégie

1. Inspecter l’énoncé exact.
2. Vérifier s’il peut consommer `C04a_squarefree_half_promoted`.
3. S’il dépend d’un résultat analytique non formalisé, ne pas forcer.
4. Le remplacer éventuellement par un bridge nommé plutôt qu’un `sorry`.

## Statut visé

```text
[O active] → [D local] ou [C bridge explicite]
```

---

# 3. `Logic/L6RatioEstimateDerived.lean` — 1 `sorry`

## Difficulté probable

🟠 **Élevée analytique**, mais peut être technique si `L6Stirling` fournit déjà l’essentiel.

## Nature

Estimation de ratio L6, probablement liée à Stirling, poids archimédien ou croissance logarithmique.

## Check-list

| Question                                                           | Test              |
| ------------------------------------------------------------------ | ----------------- |
| Existe-t-il déjà un lemme dans `AnalyticHorizon/L6Stirling.lean` ? | oui, à exploiter  |
| Le résultat est-il simplement un wrapper ?                         | possible          |
| Dépend-il d’un asymptotique non disponible ?                       | possible          |
| Est-il dans `Frozen` ?                                             | non               |
| Peut-il être rétrogradé en bridge conditionnel ?                   | oui si nécessaire |

## Points sensibles

Ligne concernée :

```text
Logic/L6RatioEstimateDerived.lean:90
```

L’ancien audit indiquait aussi des lignes autour de :

```text
stirling_ratio_asymptotic
L6RatioEstimate_derived
ZtotPositiveEventually_derived
```

## Stratégie

1. Identifier si le `sorry` porte sur `L6RatioEstimate_derived`.
2. Chercher un théorème déjà fermé dans `L6Stirling`.
3. Si le contenu est exactement “Stirling implique ratio”, faire un pont.
4. Sinon, isoler l’hypothèse analytique au lieu de fermer artificiellement.

## Statut visé

```text
[O analytique locale] → [D bridge local] ou [C]
```

---

# 4. `Analytic/GammaFactor.lean` — 4 `sorry`

## Difficulté probable

🔴 **Lourde**, chantier dédié.

## Nature

Facteur Γ / facteur archimédien / équations fonctionnelles. Un des `sorry` est dans une définition :

```text
noncomputable def D_M (s : ℂ) : ℂ := sorry
```

Ce n’est pas seulement une preuve manquante : c’est une **définition-placeholder**.

## Check-list

| Question                                                                  | Test                       |
| ------------------------------------------------------------------------- | -------------------------- |
| Les objets analytiques sont-ils définis mathématiquement ?                | à vérifier                 |
| La fonction Γ complexe est-elle disponible dans l’API locale ?            | probablement partiellement |
| Les équations fonctionnelles sont-elles classiques mais non formalisées ? | oui probable               |
| Faut-il garder ce fichier en Active ?                                     | oui                        |
| Peut-on fermer vite ?                                                     | non                        |
| Faut-il découper en interfaces ?                                          | oui                        |

## Points sensibles

Lignes concernées :

```text
Analytic/GammaFactor.lean:62
Analytic/GammaFactor.lean:83
Analytic/GammaFactor.lean:95
Analytic/GammaFactor.lean:112
```

Nature probable :

```text
- définition `D_M`
- méromorphie de γ_χ
- équation fonctionnelle γ_M
- équation fonctionnelle D_M
- équation fonctionnelle Λ_M
```

## Stratégie

Ne pas tenter une fermeture globale immédiate.

Procédure recommandée :

```text
1. Renommer clairement les placeholders.
2. Séparer :
   - définitions disponibles,
   - hypothèses analytiques,
   - théorèmes conditionnels.
3. Remplacer les `sorry` de définition par des `opaque` si l’objet est une interface.
4. Déclarer un bridge conditionnel pour les équations fonctionnelles.
5. Ne promouvoir aucun résultat en [D] avant preuve Lean réelle.
```

## Statut visé

À court terme :

```text
[sorry] → [interface conditionnelle propre]
```

À long terme :

```text
[C] → [D] si l’API analytique est construite
```

---

# 5. `AnalyticHorizon/Det2Transport.lean` — 1 `sorry`

## Difficulté probable

🔴 **Très lourde**, horizon global.

## Nature

Transport `det₂`, probablement lié à l’identification spectrale et au pont vers `ξ`.

## Check-list

| Question                                               | Test                       |
| ------------------------------------------------------ | -------------------------- |
| Dépend-il de `Det2IdentifiesXi` ?                      | probablement               |
| Dépend-il de `ZeroMatching` ?                          | possible                   |
| Est-ce une preuve locale ?                             | non                        |
| Sa fermeture impliquerait-elle une promotion globale ? | potentiellement dangereuse |
| Faut-il garder hors Frozen ?                           | oui absolument             |
| Doit-on le convertir en bridge conditionnel ?          | probablement               |

## Point sensible

Ligne concernée :

```text
AnalyticHorizon/Det2Transport.lean:71
```

## Stratégie

Ne pas chercher à fermer tant que :

```text
det₂ ↔ ξ
ZeroMatching
trace formula globale
```

ne sont pas mathématiquement établis.

Ce fichier doit rester une interface d’horizon ou un théorème conditionnel strictement borné.

## Statut visé

```text
[O] / [C]
```

Pas `[D]` à ce stade.

---

# 6. `Logic/H3/Lemma7Residual.lean` — 1 `sorry`

## Difficulté probable

⚫ **Verrou central**, ne pas traiter comme dette technique.

## Nature

Annulation du résidu sur la ligne critique.

C’est le point le plus proche du passage global problématique.

## Check-list

| Question                                               | Test                                               |
| ------------------------------------------------------ | -------------------------------------------------- |
| Est-ce une simple lacune Lean ?                        | non                                                |
| Est-ce une hypothèse analytique profonde ?             | oui                                                |
| Sa fermeture modifierait-elle le statut du programme ? | oui                                                |
| Peut-on le promouvoir par cohérence narrative ?        | non                                                |
| Peut-on le remplacer par un axiome ?                   | non, sauf bridge conditionnel explicitement marqué |
| Doit-il rester nommé ?                                 | oui                                                |

## Point sensible

Ligne concernée :

```text
Logic/H3/Lemma7Residual.lean:13
```

## Stratégie

Ne pas fermer par artifice.

Trois options seulement :

```text
1. Le laisser ouvert et nommé.
2. Le transformer en bridge conditionnel explicitement consommé.
3. Le prouver réellement, avec audit séparé et changement majeur de statut.
```

La troisième option serait un événement scientifique majeur, pas un patch ordinaire.

## Statut visé

```text
[O central]
```

---

# Ordre de fermeture recommandé

| Priorité | Cible                         | Pourquoi                                       |
| -------: | ----------------------------- | ---------------------------------------------- |
|        1 | `L10NoGoTheorem.lean`         | probablement technique, local, faible risque   |
|        2 | `RouteC.lean`                 | peut bénéficier de C-04a/C-04b fermés          |
|        3 | `L6RatioEstimateDerived.lean` | peut s’appuyer sur `L6Stirling`                |
|        4 | `GammaFactor.lean`            | chantier analytique à isoler, pas patch rapide |
|        5 | `Det2Transport.lean`          | horizon global, conditionnel                   |
|        6 | `Lemma7Residual.lean`         | verrou central, ne pas forcer                  |

---

# Check-list générale avant fermeture d’un `sorry`

Avant de remplacer un `sorry`, vérifier :

```text
[ ] L’énoncé exact est-il mathématiquement vrai ?
[ ] Le statut du module permet-il une fermeture [D] ?
[ ] La preuve n’introduit-elle aucun nouvel axiom ?
[ ] Le théorème ne dépend-il pas d’un placeholder `True` ?
[ ] Le résultat ne ferme-t-il pas implicitement RH ?
[ ] Le résultat ne ferme-t-il pas implicitement det₂ ↔ ξ ?
[ ] Le résultat ne promeut-il pas une couche Active dans Frozen sans audit ?
[ ] `lake build CouretUnification.<module>` passe.
[ ] `make audit-scripts` confirme la baisse du nombre de sorry.
[ ] Le registre documentaire est mis à jour.
```

---

# Formule de travail

```text
L10 peut être attaqué.
RouteC peut être audité.
L6 peut être raccordé.
GammaFactor doit être reconstruit.
Det2Transport doit rester conditionnel.
Lemma7Residual garde le seuil.
```

C’est l’ordre sain : fermer ce qui est fermable, nommer ce qui ne l’est pas encore, et ne jamais transformer un verrou en trophée.
