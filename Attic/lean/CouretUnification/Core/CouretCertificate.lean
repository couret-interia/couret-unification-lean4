import CouretUnification.Core.TripletToFiniteSpectrum
import CouretUnification.Core.IntegralSpectrum

namespace CouretUnification.Core

noncomputable section

/--
Le calcul harmonique du triplet distingué recolle avec le spectre
documentaire gelé dans `couretTripletSpectrum`.
-/
theorem couretTriplet_harmonic_matches_finiteSpectrum :
    tripletFourier couretTriplet =
      couretTripletSpectrum.rawHistorical.map (fun z => (z : ℂ)) := by
  exact couretTriplet_harmonic_reconstructs_finiteSpectrum

/--
Le spectre fini distingué possède bien la propriété d'intégralité
au sens documentaire fixé dans `IntegralSpectrum.lean`.
-/
theorem couretTriplet_finiteSpectrum_integral :
    hasIntegralSpectrum couretTripletSpectrum := by
  exact couretTriplet_hasIntegralSpectrum

/--
Certificat synthétique du cas Couret :
- le calcul harmonique reconstruit le spectre documentaire ;
- ce spectre est intégral au sens du noyau fini.
-/
structure CouretCertificate where
  harmonicHistorical :
    tripletFourier couretTriplet =
      couretTripletSpectrum.rawHistorical.map (fun z => (z : ℂ))
  integralFiniteSpectrum :
    hasIntegralSpectrum couretTripletSpectrum

/-- Certificat canonique du cas distingué. -/
def couretCertificate : CouretCertificate where
  harmonicHistorical := couretTriplet_harmonic_matches_finiteSpectrum
  integralFiniteSpectrum := couretTriplet_finiteSpectrum_integral

/--
Version propositionnelle compacte du certificat :
le cas Couret est harmonique-documentairement cohérent et intégral
au sens du noyau fini.
-/
theorem couretCertificate_valid :
    hasIntegralSpectrum couretTripletSpectrum := by
  exact couretCertificate.integralFiniteSpectrum

end

end CouretUnification.Core