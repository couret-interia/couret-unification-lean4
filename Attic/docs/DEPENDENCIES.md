# Graphe de dépendances T1–T7 / H3

```
T1 (FiniteCore) ← ne dépend de rien d'ouvert
  ↓
T2 (KLMN/H1) ← dépend de T1
  ↓
T3 (H3.A fonctionnel) ← dépend de T2
  ↓
T4 (Guinand-Weil scalaire) ← dépend de T3 + validation numérique
  ↓
T5 (queues Abel) ← indépendant de T1–T4 (analyse pure)
  ↓
T6 (recollement) ← consomme T5 via Integration.lean → ZeroDensityAxioms
  ↓
T7 (opérateur global) ← dépend de T6 + H3
  ↓
H3 (pont arithmétique) ← C1 (archimédien) + C2 (eulérien) + C3 (zéros)
  ↓
lock3 (Hilbert-Pólya) ← VERROU UNIQUE

Branches indépendantes :
  SymplecticObstruction ← T1 seulement
  VerifiedIntervals ← indépendant
  CouretDesics ← T1 + couche B seulement
```
