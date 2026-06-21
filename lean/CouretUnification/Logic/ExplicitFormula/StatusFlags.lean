/-
  CouretUnification.Logic.ExplicitFormula.StatusFlags
  ════════════════════════════════════════════════════════════════════
  Drapeaux doctrinaux locaux pour la couche `ExplicitFormula`.

  Ce fichier expose des booléens de garde indiquant explicitement ce que
  la couche de formule explicite NE revendique PAS.

  Rôle :
    • empêcher toute ambiguïté sur le statut de la couche ;
    • rendre visibles les non-revendications globales ;
    • fournir des constantes simples réutilisables par les fichiers
      d'interface ;
    • préserver la séparation entre architecture formelle et preuve
      analytique complète.

  Garde-fous :
    • aucune revendication RH ;
    • aucun certificat Hilbert–Pólya ;
    • aucun candidat C déclaré fermé ;
    • aucun pont de formule explicite déclaré analytiquement clos.

  Statut :
    interface de drapeaux ;
    aucune preuve analytique ;
    aucune conséquence globale.
-/

namespace CouretUnification.Logic.ExplicitFormula

/-- Aucune revendication de l'Hypothèse de Riemann n'est exportée. -/
def RHClaimed : Bool := false

/-- Aucun certificat Hilbert–Pólya n'est revendiqué. -/
def HilbertPolyaClaimed : Bool := false

/-- Le candidat C demeure prospectif / ouvert. -/
def CandidateCClaimed : Bool := false

/-- Le pont de formule explicite est architectural, non une preuve analytique complète. -/
def ExplicitFormulaClaimedAsClosed : Bool := false

end CouretUnification.Logic.ExplicitFormula
