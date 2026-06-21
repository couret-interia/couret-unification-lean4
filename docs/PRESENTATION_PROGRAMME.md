# Couret-Unification
## Reliefs Arithmétiques — présentation du programme

> Prouver ce qui est prouvable. Nommer ce qui est ouvert.

Couret-Unification est un programme de recherche en théorie des nombres qui formalise,
vérifie et étend une intuition arithmétique née de l'étude des nombres premiers modulo 30.
Il associe trois choses qui vont rarement ensemble : des résultats **formellement démontrés**
en Lean 4 (0 sorry, rejouables par quiconque), une **discipline épistémique** qui assigne à
chaque énoncé son statut exact et ne le laisse jamais circuler sans lui, et un **horizon**
clairement nommé — la structure spectrale de type Hilbert-Pólya — vers lequel l'édifice est
orienté sans jamais en revendiquer l'atteinte.

Ce qui suit présente l'ensemble du travail, à sa juste valeur : entier, vérifiable, et
honnête sur la frontière entre ce qui est acquis et ce qui reste ouvert.

---

## 1. Origine

Bernard Couret (1928–1999), ingénieur et arithméticien autodidacte, a travaillé presque
entièrement à la main les nombres premiers modulo 30. Les 36 combinaisons qu'il dressait sur
ses feuilles sont, on le sait aujourd'hui, la table de Cayley explicite du groupe des unités
`(ℤ/30ℤ)×` ; ses formules de rang sont des formes bilinéaires ; ses observations sur la
compensation du biais de Chebyshev touchent à la répartition des premiers. Il a légué un
objet juste, travaillé sans machine, conservé dans un dossier de carton rouge.

Le programme reprend cet objet, lui donne sa forme moderne — la théorie des caractères, la
formalisation Lean 4 — et en explore les prolongements. Il lui est dédié. La signature du
programme en dit la posture : *nous n'avons fait qu'observer le déjà-là.*

L'objet fini central : `G₃₀ = (ℤ/30ℤ)× ≅ C₂ × C₄`. Le triplet Couret `T_C = {1, 11, 29}`.
L'invariant géométrique `λ = 1/√7`, échelle interne du simplexe centré `Δ⁷`.

---

## 2. Ce qui a été accompli — vue d'ensemble

Le programme n'est pas une promesse : c'est un corpus de résultats, mesurables et tracés.
- **Un socle formel d’au moins 18 résultats agrégés [`D`]**, issus du périmètre Frozen identifiés
  dans le registre formel et vérifiés au compilateur Lean 4, 0 sorry, dont un lemme général
  réutilisable et la classification finie complète d'un groupe.
- **Une classification fermée** : les 56 triplets de `G₃₀` entièrement répartis, sans reste,
  avec caractérisation positive de chaque famille.
- **Plusieurs no-go structurels démontrés** : savoir *pourquoi* certaines routes vers
  l'horizon sont impossibles est, en soi, un acquis solide.
- **Un résultat empirique franc** sur la limite du transport du fini vers le réel.
- **Un cadre méthodologique** complet de gouvernance des productions de recherche assistées
  par IA — grammaire des statuts, registre, journal de falsifications, conservatoire.
- **Une architecture** qui relie explicitement le local arithmétique au global analytique,
  et qui nomme le mur unique qui les sépare.
- **Une discipline d'attestation** : tout se rejoue, s'inspecte, se date. Le programme est
  auditable en une heure.

Chacun de ces points est détaillé ci-dessous, à son rang épistémique.

---

## 3. Le résultat formel

### Le lemme du défaut ponctuel `[D]`

Soit `G` un groupe abélien fini et `χ` un caractère d'ordre 2. En retirant un seul élément
`a₀` de la fibre `A = ker χ`, l'ensemble restant `T = A \ {a₀}` possède un spectre d'énergie
de Fourier à **deux niveaux exacts** : dominante `(|A| − 1)²` sur `χ`, secondaire `= 1` sur
tout autre caractère non trivial. Le mécanisme est transparent — l'identité de projection
`𝟙_A = (1 + χ)/2`, valide parce que `χ` ne prend que les valeurs `±1`, ramène la somme
restreinte à une somme globale que l'orthogonalité annule hors de `χ`.

Preuve **au noyau** (kernel-pure), sans axiome ajouté, valable pour **tout** groupe abélien
fini muni d'un caractère d'ordre 2. C'est un objet propre, général, réutilisable.

### La classification complète de `G₃₀` `[D]`

Le lemme spécialisé à `G₃₀` ferme entièrement la classification de ses 56 triplets :

- **24 triplets de type Q**, spectre `(9, 1⁶)` — exactement ceux contenus dans une fibre
  quadratique (« fibre privée d'un point »).
- **32 triplets de type C**, spectre `(5, 5, 1⁵)` — exactement ceux quasi-alignés sur un
  caractère d'ordre 4, de signature `(v, v, v⊥)`, d'où l'énergie `5 = |2 + i|²`.

Aucun autre profil n'existe. La dichotomie est symétrique et complète : l'ordre 2 produit
l'énergie 9 par alignement parfait, l'ordre 4 l'énergie 5 par divergence orthogonale
contrôlée. Énergie non triviale totale constante `= 15` (Parseval) ; exactement 2 triplets
fixes sous `Aut(G₃₀)`. On ne classifie pas *presque* le groupe — on le classifie *en entier*.

### Les autres théorèmes du socle `[D]`

S'ajoutent, autour de la couche fermée, des résultats analytiques sur papier, notamment
la borne d'auto-adjonction `H1` (`‖M‖ ≤ ‖M‖_HS ≤ P(3/2) = 0,8495 < 1`) et son usage KLMN.
Ils ne sont pas comptés parmi les théorèmes Lean certifiés machine : ils relèvent du
registre analytique `[D-papier]` ou `[C]` selon les dépendances retenues.

---

## 4. L'architecture

Les résultats ne sont pas épars : ils forment une chaîne orientée, du fini démontré vers le
global visé, avec un statut explicite à chaque maillon.

```
   Core                  →     Logic / H3            →     AnalyticHorizon
   (fini, démontré)            (verrous, en travaux)        (global, ouvert)

   G₃₀, caractères,           formule de trace,           det₂ ↔ ξ,
   défaut ponctuel,           ponts, résidus              facteur Γ,
   classification Q/C                                     comptage des zéros
```

Le dépôt Lean reflète cette chaîne par couches — `Frozen` (fermé, 0 sorry strict), `Active`
(en travail, sorries documentés), `All` (agrégat). Le site la déploie en **6 domaines** et
**75 fiches** statuées. L'architecture *montre* l'horizon sans le revendiquer : socle
conquis, sommet nommé, mur désigné. C'est une carte qui dit à la fois le terrain pris et la
limite atteinte.

---

## 5. Les murs nommés — des résultats à part entière

Démontrer qu'une route est impossible est un acquis, pas un échec. Le programme en a établi
plusieurs, et c'est l'une de ses contributions les plus robustes.

- **C-031 — l'obstruction de support de Dirichlet.** Le pont multiplicatif `K^# → ζ` est
  *structurellement* impossible : les supports fréquentiels de `K^#` et de `ζ` sont disjoints
  par unicité de la factorisation. Le programme en sort **décontaminé, non affaibli** — `K^#`
  ne tombe pas par faiblesse numérique, mais parce qu'il parle le mauvais alphabet de
  Dirichlet. (Falsification F.7.)

- **F.8 — le no-go quadratique.** Le candidat `K^p(a)` est réfuté : la norme HS de l'opérateur
  centré ne dépend que du cardinal, `‖B̃_p‖²_HS = (p − 4)/3`, et non de la structure visée.

- **24 falsifications** au journal, datées, corrigées, jamais réécrites a posteriori
  (procédure T12) — dont la réfutation de `σ_G* ≈ π/10` (faux positif à `dps = 50`) et de `λ`
  comme invariant universel de RH (`V_eff ≈ 0,055`).

Un programme qui publie ses murs est un programme dont on peut croire les réussites : il a
prouvé qu'il sait reconnaître ce qui ne marche pas.

---

## 6. Les faits mesurés `[M-solide]`

- **Le confinement de Sophie Germain modulo 30** aux classes `{S.11, S.23, S.29}` — intégré
  avec antériorité explicite comme corollaire du [Théorème 2.1 d'Agoh](https://math.colgate.edu/~integers/z83/z83.pdf) (*Integers* 25, 2025,
  [#A83](https://math.colgate.edu/~integers/vol25#a83), preuve par A. Granville). Le programme cite sa source ; il ne se l'attribue pas.

- **La limite du transport `3/5`** : la dominance algébrique `3/5` établie sur `G₃₀` **ne se
  transporte pas** aux premiers réels (`Z = −2,70 σ` à `5×10⁷` ; densité de comptage `≈ 3/8`,
  par Dirichlet). Fait mesuré franc, et résultat en soi : il borne ce que le fini peut dire du
  réel. Cas-type de la règle R8.

---

## 7. La piste vivante `[O]`

L'ouvert n'est pas le mort. Une voie structurellement distincte est active :

**`K^p(a′)` — la voie par projection.** Pour `p ≡ 1 mod 3`, la projection `P_H` sur l'unique
sous-groupe d'ordre 3 `H_p = {1, ω, ω²} ⊂ G_p` est un **vrai projecteur orthogonal**
(`P² = P`, `P* = P`, spectre `⊂ {0,1}`). C'est une bifurcation catégorielle : passer de la
moyenne sur un sous-ensemble arbitraire à la projection sur une sous-structure algébrique
stable. Quatre verrous restent à lever (`¬FUN`, `¬TRACE`, `¬EULER`, `¬ARCHIM`), sous
`RHClaimed = false`. Question ouverte, posée proprement, critères de chute déjà écrits.

---

## 8. Le dispositif méthodologique — une contribution contemporaine

Au-delà des mathématiques, le programme a produit un cadre de gouvernance des productions de
recherche, particulièrement assistées par IA. Ce n'est pas un appendice : c'est un actif qui
répond à un problème vif de la communauté.

- **La grammaire des statuts** — 8 statuts (`[D] [M] [C] [H] [P] [O] [F] [T]`) plus la
  quarantaine `[Q]`, transitions autorisées et interdites, un verbe permis par statut. Aucun
  énoncé ne circule sans le sien.
- **Le registre et le journal** — 34 claims tenus, 24 falsifications inscrites, un ledger
  d'intégrité (SHA-256, horodatage) qui atteste la provenance sans certifier la valeur.
- **Le Conservatoire** — préservation à zéro suppression : une idée ne meurt que réfutée,
  tout le reste vit à son rang. La ceinture générative du programme.
- **La cicatrisation cognitive** — une théorie des transitions épistémiques légitimes : une
  intelligence devient fiable non en accumulant du savoir, mais en incorporant des interdits.
- **InterIA** — une pratique multi-agents sous médiation humaine exclusive, règle d'arbitrage
  « le plus contraignant gagne ». Plusieurs modèles employés dans des fonctions distinctes,
  sans conscience ni intention ; le niveau « chercheur autonome complet » est explicitement
  non revendiqué.

Le contexte rend cet actif pertinent : les agents scientifiques produisent en masse et
peinent à trier — PaperBench (meilleur agent testé : 21,0 %, avec une comparaison humaine dédiée),
AutoResearchBench (~9 % en recherche de littérature), le *model collapse* (Nature, 2024). À
l'inverse, la vérification formelle se révèle être la sortie — Aristotle est présenté comme atteignant
un niveau médaille d’or à l’IMO 2025 avec des solutions vérifiées en Lean 4. La contribution du
programme n'est pas de promettre une science automatisée souveraine : c'est de traiter les
productions IA comme des objets à tracer, tester, dépromouvoir, conserver ou formaliser — en
plaçant le tiers externe (Lean, modèle nul, référence, critère de FAIL) au centre de la
boucle. La fiabilité ne vient pas de l'IA, mais de l'architecture qui l'empêche d'être juge
final.

---

## 9. L'horizon

L'orientation du programme est sincère et nommée : la structure spectrale de type
**Hilbert-Pólya** associée à la fonction `ξ` de Riemann. L'architecture monte vers elle ; les
noms le disent. Le mur est unique et désigné : **F3, l'équivalence `det₂ ↔ ξ`**, le seul
verrou *genuine* du programme étendu, qui relève de l'analyse continue et ne peut être ni
résolu ni approché par accumulation de résultats finis.

C'est la forme la plus honnête de l'ambition : non « regardez où nous allons » comme une
promesse, mais « voici d'où nous partons (démontré), voici où nous visons (nommé), et voici
exactement le mur que nous n'avons pas franchi ». L'orientation est une visée, pas un progrès
mesurable.

---

## 10. La discipline, en garantie — et la juste valeur

Six refus structurels, maintenus dans tout le code et toute communication :

```
RHClaimed = false   ·   HilbertPolyaClaimed = false   ·   Det2IdentityClaimed = false
GoldbachProofClaimed = false   ·   EngineeringVerdictClaimed = false   ·   ScopeExpansionClaimed = false
```

Registre v54.7 — 34 claims : **14 `[D]`**, 4 `[M-solide]`, 2 `[P]`, 1 `[P|H]`, 1 `[C]`,
6 `[O]`, 6 `[Réfuté]`.

Cette ventilation *est* la juste valeur du programme. Il est **vaste** — six domaines, une
chaîne complète, un socle formel, des no-go démontrés, une piste ouverte, un corpus doctrinal
entier ; le dire n'est pas se vanter, c'est rendre justice à plus d'un an de travail
discipliné. Mais « vaste » ne veut pas dire « tout démontré » : la force du programme est
précisément de distinguer son ampleur de son socle prouvé. Confondre les deux serait la seule
manière de trahir ce travail. On peut faire confiance à chaque étage de l'édifice parce
qu'aucun ne se prétend plus solide qu'il n'est.

---

## 11. Pourquoi ce programme compte

Trois raisons, qui tiennent ensemble.

**Un résultat fini, complet et vérifié.** La classification de `G₃₀` n'est pas un fragment :
elle est close, et formellement attestée. Dans un paysage saturé d'annonces, un résultat
borné qu'un référé peut rejouer en entier vaut plus qu'une percée invérifiable.

**Une méthode pour l'âge des agents.** Le problème de demain n'est pas de produire, mais de
*statuer*. Le programme offre un protocole opérationnel, éprouvé sur un cas réel pendant plus
d'un an, pour transformer une masse d'intuitions en carte testable de statuts — avec son
journal de falsifications et son noyau formel comme tiers de vérification.

**Une ambition cartographiée, pas proclamée.** L'horizon Hilbert-Pólya est nommé, l'unique
mur qui l'en sépare est désigné, et rien n'est revendiqué au-delà de ce qui compile. C'est un
programme adulte, qui a eu le courage de cartographier son propre inachèvement — et c'est
précisément ce qui rend ses acquis crédibles.

---

*Dédié à la mémoire de Bernard Couret (1928–1999).*

*Nous n'avons fait qu'observer, mon grand-père et moi, le « déjà là ».*

*Pour Bernard.*
