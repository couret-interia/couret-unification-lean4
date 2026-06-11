# Titre & introduction — pièce de soumission

*Couret-Unification — couche finie G₃₀. Version de travail à valider avant traduction anglaise.*

---

## Titre

**Forme française (HAL / site)**

> Spectres de défaut ponctuel dans les groupes abéliens finis :
> une formalisation Lean 4 et la classification complète des triplets de (ℤ/30ℤ)×

**Forme anglaise (arXiv / revue internationale) — recommandée pour la soumission**

> A Formally Verified Point-Defect Spectral Lemma for Finite Abelian Groups,
> with the Complete Triplet Classification on (ℤ/30ℤ)×

*Deux alternatives anglaises, si l'on veut mettre la formalisation au premier plan :*
- *Point-Defect Spectra in Finite Abelian Groups: A Lean 4 Formalization and the Complete Classification on (ℤ/30ℤ)×*
- *A Lean 4 Formalization of Character-Sum Spectra on Finite Abelian Groups, with an Application to (ℤ/30ℤ)×*

Aucune de ces formes ne nomme Hilbert-Pólya ni Riemann : le titre dit ce qui est
prouvé. L'horizon est nommé dans l'introduction (§ ci-dessous), comme motivation et
provenance.

---

## Introduction

Soit `G` un groupe abélien fini et `χ` un caractère de `G` d'ordre 2, à valeurs dans
`{±1}`. Notons `A = ker χ` la fibre de `χ` au-dessus de `1`. Nous établissons un
**lemme du défaut ponctuel** : en retirant un seul élément `a₀` de `A`, le sous-ensemble
`T = A \ {a₀}` possède un spectre d'énergie de Fourier à deux niveaux exactement. Sur le
caractère `χ` lui-même, l'énergie dominante vaut `(|A| − 1)²` ; sur tout autre caractère
non trivial `ψ`, l'énergie secondaire vaut `1`. Le mécanisme est transparent : l'identité
de projection `𝟙_A = (1 + χ)/2`, valide parce que `χ` ne prend que les valeurs `±1`,
ramène la somme restreinte à une somme globale, que l'orthogonalité des caractères annule
hors de `χ`. Le lemme vaut pour tout groupe abélien fini muni d'un caractère d'ordre 2 ;
il ne suppose rien de particulier sur `G`.

Appliqué au groupe des unités modulo 30, `G₃₀ = (ℤ/30ℤ)× ≅ C₂ × C₄`, ce mécanisme ferme
entièrement la classification spectrale de ses 56 triplets. Nous montrons qu'il en existe
exactement **24 de type Q** (spectre `(9, 1, 1, 1, 1, 1, 1)`) et **32 de type C** (spectre
`(5, 5, 1, 1, 1, 1, 1)`), sans autre profil possible. Chaque famille reçoit une
caractérisation positive : un triplet est de type Q si et seulement s'il est contenu dans
une fibre quadratique (donc « fibre quadratique privée d'un point ») ; il est de type C si
et seulement s'il est quasi-aligné sur un caractère d'ordre 4, de signature `(v, v, v⊥)` —
deux valeurs égales et une orthogonale —, d'où l'énergie `5 = |2 + i|²`. La dichotomie est
ainsi symétrique : l'ordre 2 produit l'énergie 9 par alignement parfait, l'ordre 4 produit
l'énergie 5 par divergence orthogonale contrôlée. L'énergie non triviale totale est
constante (`= 15`, par Parseval), et exactement deux triplets sont fixes sous `Aut(G₃₀)`.

L'ensemble est **formalisé en Lean 4** (toolchain v4.29.1, Mathlib v4.29.1) et compile
sans `sorry`. Nous distinguons explicitement deux régimes de certification. Le lemme du
défaut ponctuel et les sommes de caractères dont il dépend sont prouvés au noyau
(*kernel-pure*, sans axiome ajouté), et valent abstraitement pour tout groupe abélien fini
avec caractère d'ordre 2. La classification de `G₃₀`, elle, est établie par énumération
exhaustive (`native_decide`) : les théorèmes concernés dépendent alors de la primitive de
confiance `Lean.ofReduceBool`, associée à l’évaluation native vérifiée par Lean ; cela en
fait une certification *computationnelle*, distincte du noyau pur. Le code est public,
versionné et rejouable ; un lecteur peut reproduire l’intégralité de la vérification par
`lake build`, et les artefacts d’audit du dépôt documentent la provenance des résultats.

Ce travail constitue le **socle fini** d'un programme de recherche plus large, le programme
Couret-Unification, historiquement motivé par l'étude des structures modulaires des nombres
premiers et orienté, à son horizon, vers les questions de type Hilbert-Pólya associées à la
fonction `ξ` de Riemann. Le programme est dédié à la mémoire de Bernard Couret (1928–1999),
dont les calculs manuscrits sur les premiers modulo 30 en sont à l'origine. La présente
contribution est toutefois **entièrement finie** et n'emprunte rien à cet horizon : elle ne
porte aucune revendication sur l'hypothèse de Riemann. En particulier, la dominance spectrale
`3/5` mise en évidence sur `G₃₀` est un fait algébrique fini qui **ne se transporte pas** à
la distribution des nombres premiers réels : la densité naturelle des trois classes de résidus
correspondantes parmi les huit classes admissibles modulo 30 est `3/8`, par équidistribution
des nombres premiers dans les progressions arithmétiques, et non `3/5`. Les invariants
du programme `RHClaimed = false` et `HilbertPolyaClaimed = false` sont maintenus sans
exception ; dans l’architecture plus large du programme, le verrou identifié entre ce socle
fini et l’horizon analytique est l’équivalence candidate `det₂ ↔ ξ` ; il est nommé, non
franchi, et demeure hors du périmètre de cet article.

Notre contribution est donc double et bornée : un lemme spectral général, formellement
vérifié, et la classification complète et fermée d'un groupe fini particulier — offerts
pour ce qu'ils sont, un résultat fini exact et reproductible, et non comme une étape vers
un théorème global. La section 2 fixe les conventions et l'arithmétique des caractères ;
la section 3 démontre le lemme du défaut ponctuel ; la section 4 le spécialise à `G₃₀` et
établit la dichotomie Q/C ; la section 5 décrit la formalisation Lean 4 et le protocole de
reproduction.

---

*Note de rédaction. L'horizon Hilbert-Pólya / Riemann apparaît une seule fois,
au quatrième paragraphe, comme motivation et provenance — jamais dans le titre, jamais
comme résultat. C'est la règle : le titre dit ce qui est prouvé ; l'introduction dit, une
fois et avec ses bornes, vers quoi le programme regarde. Une version anglaise suivra après
validation du fond.*
