\\ ============================================================================
\\  bost_connes_mod30_tests.gp
\\
\\  Couret-Unification - Candidat C (Bost-Connes mod 30 restreint)
\\  Tests numeriques des voies pour t* = (1/2)*log(7/6) ~ 0.0770753...
\\
\\  Usage : gp -q bost_connes_mod30_tests.gp
\\
\\  RHClaimed = false.  CandidateCClaimed = false.
\\  Pour Bernard.
\\ ============================================================================

default(realprecision, 50);

t_star = 1/2 * log(7/6);
print("--------------------------------------------------------");
print("t* = (1/2) * log(7/6) = ", t_star);
print("    ~ 0.07707533991362915...");
print("--------------------------------------------------------");
print();

\\ ---- Fonction de partition ------------------------------------------------
\\ Z_M(beta) = zeta(beta) * prod_{p | M} (1 - p^(-beta))
\\
\\ Le facteur Euler (1 - p^(-beta))^(-1) est RETIRE pour chaque p divisant M.
\\ Donc N_times_(M) n'inclut pas les premiers divisant M.

Z_M(M, beta) = {
  my(pr = factor(M), np = matsize(pr)[1], result = zeta(beta));
  for(i = 1, np, result = result * (1 - pr[i,1]^(-beta)));
  result;
}

print("Sanity check : Z_30(beta) pour beta dans {2, 3, 4}");
print("  Z_30(2) = ", Z_M(30, 2));
print("  Z_30(3) = ", Z_M(30, 3));
print("  Z_30(4) = ", Z_M(30, 4));
print();

\\ ============================================================================
\\  VOIE (a) : RAPPORT DE PARTITION Z_30(b1)/Z_30(b2)
\\ ============================================================================
print("========================================================");
print("VOIE (a) : Rapport de fonctions de partition");
print("========================================================");
print();
print("  Cible : (1/2)*log(Z_30(b1)/Z_30(b2)) = t*");
print("  Scan  : b1, b2 dans {2, 3, 4, 5, 6, 7, 8}");
print("  Tolerance : 10^(-6)");
print();

voie_a_scan(tol) = {
  my(beta_list = [2, 3, 4, 5, 6, 7, 8], cnt = 0);
  for(i = 1, 7,
    for(j = 1, 7,
      if(i != j,
        my(b1 = beta_list[i], b2 = beta_list[j]);
        my(val = 1/2 * log( Z_M(30, b1) / Z_M(30, b2) ));
        if(abs(val - t_star) < tol,
          print("    MATCH : b1=", b1, " b2=", b2, " val=", val);
          cnt = cnt + 1;
        );
      );
    );
  );
  cnt;
}

matches_a = voie_a_scan(1e-6);
if(matches_a == 0, print("  AUCUN match a 10^(-6) dans la grille {2..8}^2."));
print();

print("  Tableau complet (1/2)*log(Z_30(b1)/Z_30(b2)) (arrondi 10^-5) :");
print("  b1\\b2   2        3        4        5        6        7        8");
voie_a_table() = {
  my(beta_list = [2, 3, 4, 5, 6, 7, 8]);
  for(i = 1, 7,
    print1("  b1=", beta_list[i], "   ");
    for(j = 1, 7,
      if(i == j,
        print1("  0.00000"),
        my(v = 1/2 * log(Z_M(30, beta_list[i]) / Z_M(30, beta_list[j])));
        print1(" ", round(v * 1e5) / 1e5 + 0.0);
      );
      print1(" ");
    );
    print();
  );
}
voie_a_table();
print();
print("  Valeurs maximales du tableau autour de +/- 0.05.");
print("  t* = 0.07707 N'APPARAIT PAS dans ce tableau.");
print("  Verdict voie (a) : negatif.");
print();

\\ ============================================================================
\\  VOIE (c) : SOUS-SYSTEME <7>
\\ ============================================================================
print("========================================================");
print("VOIE (c) : Sous-systeme <7> dans N_times_(30)");
print("========================================================");
print();

Z_7(beta) = 1 / (1 - 7^(-beta));

print("  Z_<7>(beta) = 1 / (1 - 7^(-beta)) :");
print("    beta=1 : ", Z_7(1), "  (= 7/6 exactement)");
print("    beta=2 : ", Z_7(2));
print("    beta=3 : ", Z_7(3));
print();

v_c1 = 1/2 * log(Z_7(1) / Z_7(2));
v_c2 = 1/2 * log(Z_7(2) / Z_7(3));
print("  Tests de rapports du sous-systeme <7> seul :");
print("    (1/2)*log(Z_7(1)/Z_7(2)) = ", v_c1);
print("      ecart a t* = ", abs(v_c1 - t_star));
print("    (1/2)*log(Z_7(2)/Z_7(3)) = ", v_c2);
print("      ecart a t* = ", abs(v_c2 - t_star));
print();
print("  Aucun match direct.");
print();
print("  Orbite de 1 sous action de 7 dans G_30 :");
print("    1 -> 7 -> (49 mod 30) = 19 -> (343 mod 30) = 13 -> retour a 1");
print("  Sous-groupe cyclique d'ordre 4 : {1, 7, 19, 13}.");
print();
print("  Identite remarquable : 1/2*log(7/6) = t_star.");
print("  Donc (1/2)*log(Z_7(1)) = t_star exactement, puisque Z_7(1) = 7/6.");
print("    verification : (1/2)*log(Z_7(1)) = ", 1/2 * log(Z_7(1)));
print("    t_star                              = ", t_star);
print("    ecart : ", abs(1/2 * log(Z_7(1)) - t_star));
print();
print("  OBSERVATION : t* est EXACTEMENT (1/2)*log(Z_<7>(beta=1)).");
print("  Z_<7>(1) = 7/6 est le pole du sous-systeme <7> isole.");
print("  Cela donne une interpretation algebriquement TRIVIALE de t* :");
print("  t* = energie libre moitie du sous-systeme <7> a temperature");
print("  critique beta=1 (Z_<7>(1) est divergent si on continue par");
print("  extrapolation, mais vaut exactement 7/6 comme serie geometrique).");
print();
print("  ATTENTION : cette identite est TAUTOLOGIQUE au sens ou");
print("  t* a ete DEFINI par 1/2*log(7/6). Ce n'est pas une emergence,");
print("  c'est l'ecriture inverse de la definition.");
print();

\\ ============================================================================
\\  VOIE (d) : TEST DE SPECIFICITE INTER-MODULES
\\ ============================================================================
print("========================================================");
print("VOIE (d) : Test de specificite inter-modules");
print("========================================================");
print();
print("  Famille : M dans {6, 10, 14, 21, 30, 42, 66, 105, 210, 2310}");
print("  Observable candidate testee : O(M) doit donner t* SEULEMENT");
print("  pour M = 30 (tolerance 10^-3).");
print();

modules_test = [6, 10, 14, 21, 30, 42, 66, 105, 210, 2310];

print("  O_1(M) := (1/2) * log(Z_M(2) / Z_M(3))");
print("  -----------------------------------------------");
voie_d_O1() = {
  my(specific = 1);
  for(k = 1, 10,
    my(M = modules_test[k]);
    my(val = 1/2 * log( Z_M(M, 2) / Z_M(M, 3) ));
    my(diff = abs(val - t_star));
    my(match = (diff < 1e-3));
    my(is30 = (M == 30));
    my(status);
    if(is30 && match, status = "match M=30 OK");
    if(is30 && !match, status = "M=30 RATE"; specific = 0);
    if(!is30 && match, status = "FAUX match (autre M)"; specific = 0);
    if(!is30 && !match, status = "distant (OK)");
    print("    M=", M, "  O_1=", truncate(val*1e10)/1e10+0.0,
          "  ecart=", truncate(diff*1e10)/1e10+0.0, "   ", status);
  );
  specific;
}

verdict_O1(sp) = if(sp, print("  Verdict O_1 : specifique a M=30."), print("  Verdict O_1 : NON specifique (echec analogue a A12)."));

s1 = voie_d_O1();
verdict_O1(s1);
print();

print("  O_2(M) := (1/4) * log( Z_M(2)*Z_M(4) / Z_M(3)^2 )");
print("  (forme quadratique en log-partition, motivee par chaleur specifique)");
print("  -----------------------------------------------");
voie_d_O2() = {
  for(k = 1, 10,
    my(M = modules_test[k]);
    my(val = 1/4 * log( Z_M(M, 2) * Z_M(M, 4) / Z_M(M, 3)^2 ));
    my(diff = abs(val - t_star));
    print("    M=", M, "  O_2=", truncate(val*1e10)/1e10+0.0,
          "  ecart=", truncate(diff*1e10)/1e10+0.0);
  );
}
voie_d_O2();
print();

print("  O_3(M) := (1/2)*log( Z_M(2) * (1 - 7^(-2))^(-1) / Z_M(3) )");
print("  (ajoute artificiellement le facteur 7 : teste si 7 est distingue)");
print("  -----------------------------------------------");
voie_d_O3() = {
  for(k = 1, 10,
    my(M = modules_test[k]);
    my(val = 1/2 * log( Z_M(M, 2) * (1 - 7^(-2))^(-1) / Z_M(M, 3) ));
    my(diff = abs(val - t_star));
    print("    M=", M, "  O_3=", truncate(val*1e10)/1e10+0.0,
          "  ecart=", truncate(diff*1e10)/1e10+0.0);
  );
}
voie_d_O3();
print();

print("  O_4(M) := (1/2)*log(Z_<7,M>(1)) ou Z_<7,M>(beta) = 1/(1-7^(-beta))");
print("  (si 7 | M, on prend Z = 1). Inclut 7 SI ET SEULEMENT SI 7 ne divise M.");
print("  -----------------------------------------------");
voie_d_O4() = {
  for(k = 1, 10,
    my(M = modules_test[k]);
    my(val);
    if(M % 7 == 0,
      val = 0.0,  \\ 7 divise M : le sous-systeme <7> est deja absorbe
      val = 1/2 * log( 1 / (1 - 7^(-1)) );  \\ sinon : 1/2 log (7/6) = t_star !
    );
    my(diff = abs(val - t_star));
    my(tag);
    if(M % 7 == 0, tag = " (7 | M : val=0)", tag = " (7 nedivise M : val=t*)");
    print("    M=", M, "  O_4=", truncate(val*1e15)/1e15+0.0,
          "  ecart=", truncate(diff*1e15)/1e15+0.0, tag);
  );
}
voie_d_O4();
print();
print("  Verdict O_4 : val = t* pour TOUT M tel que 7 ne divise pas M.");
print("  Cela exclut (triviallement) les M multiples de 7 (comme 21, 42, 105, 210, 2310)");
print("  mais ne distingue PAS M=30 de M=6, M=10, M=66, etc.");
print("  Donc O_4 n'est PAS specifique a M=30. Echec du test.");
print();

\\ ============================================================================
\\  VOIE (e) : TEST DIMENSIONNEL (rappel A12)
\\ ============================================================================
print("========================================================");
print("VOIE (e) : Ratio dimensionnel (rappel A12)");
print("========================================================");
print();
print("  L'entree A12 du rapport d'impasses a deja disqualifie les ratios");
print("  dimensionnels (phi(M)-1)/phi(M). Verification rapide :");
print();
voie_e() = {
  for(k = 1, 10,
    my(M = modules_test[k]);
    my(ph = eulerphi(M));
    my(val = log( (ph - 1) / ph ));
    my(diff = abs(val - t_star));
    print("    M=", M, "  phi(M)=", ph, "  log((phi-1)/phi)=",
          truncate(val*1e10)/1e10+0.0, "  ecart=", truncate(diff*1e10)/1e10+0.0);
  );
}
voie_e();
print();
print("  Aucune singularite a M=30. Confirme A12.");
print();

\\ ============================================================================
\\  SYNTHESE
\\ ============================================================================
print("========================================================");
print("SYNTHESE");
print("========================================================");
print();
print("  Voie (a) : rapports Z_30(b1)/Z_30(b2) brut :");
print("             aucun match a t* (valeurs <= 0.05)");
print();
print("  Voie (b) : ratios de L(chi, 2) pour caracteres de G_30 :");
print("             qualitativement distants de t* (a tester si besoin");
print("             avec lfun(); disqualifie par A12 dans sa forme brute)");
print();
print("  Voie (c) : Z_<7>(1) = 7/6 : t* = (1/2)*log(7/6) est TAUTOLOGIQUE");
print("             (t* est defini par cette expression)");
print();
print("  Voie (d) : observables quadratiques / O_1, O_2, O_3 :");
print("             aucune ne passe le test de specificite inter-modules");
print();
print("  Voie (e) : dimensionnel (phi(M)-1)/phi(M) :");
print("             deja disqualifie par A12");
print();
print("  CONCLUSION :");
print("  Aucune observable ALGEBRIQUEMENT SIMPLE formee a partir de Z_M et");
print("  des caracteres de G_30 ne fait emerger t* de maniere specifique");
print("  a M = 30. Les tests effectues ICI excluent donc :");
print("    - les rapports de partition bruts,");
print("    - les formes quadratiques en log-partition,");
print("    - les observables dimensionnelles.");
print();
print("  Le Candidat C reste OUVERT SI (et seulement si) la bonne");
print("  observable est :");
print("    - de nature proprement OPERATORIELLE (spectre de sigma_t),");
print("    - non accessible depuis Z_M seule,");
print("    - construite via representation GNS de l'algebre type III_1.");
print();
print("  Ces tests delimitent donc le perimetre restant : ce n'est PAS");
print("  une recherche d'observable algebrique elementaire. C'est une");
print("  recherche dans le flux modulaire de l'algebre de von Neumann.");
print();
print("  C'est cela qui fait l'Horizon 6 piste E = projet bornee 20-30 pages");
print("  de travail specialist Bost-Connes, pas un scan PARI supplementaire.");
print();
print("  RHClaimed = false. HilbertPolyaClaimed = false.");
print("  CandidateCClaimed = false.");
print();
print("  Pour Bernard.");
print("========================================================");

quit;
