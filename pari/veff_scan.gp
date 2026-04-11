\\ veff_scan.gp
\\ Balayage automatique de V_eff pour plusieurs T_max
\\ Usage:
\\   gp -s 256000000 -D parisizemax=4000000000 < pari/veff_scan.gp

default(realprecision, 38);

V_from_L(L, T) =
{
  my(z, s = 0.0);
  z = lfunzeros(L, T);
  for(j = 1, #z, s += 2.0 / (0.25 + z[j]^2));
  return([#z, s]);
};

compute_V_values(T_max) =
{
  my(V_values, res, idx, G15, k15, G0, chi0);

  V_values = vector(8);

  \\ 1) caractère trivial
  res = V_from_L(1, T_max);
  V_values[1] = res[2];

  \\ 2) caractère non trivial mod 3
  res = V_from_L(Mod(2, 3), T_max);
  V_values[5] = res[2];

  \\ 3) caractères non triviaux mod 5 : labels 2,3,4
  idx = 2;
  for(m = 2, 4,
    res = V_from_L(Mod(m, 5), T_max);
    V_values[idx] = res[2];
    idx++;
  );

  \\ 4) caractères primitifs de conducteur 15
  G15 = znstar(15, 1);
  k15 = 0;
  for(m = 1, 14,
    if(gcd(m, 15) == 1,
      [G0, chi0] = znchartoprimitive(G15, m);
      if(G0.mod == 15,
        k15++;
        res = V_from_L(Mod(m, 15), T_max);
        V_values[5 + k15] = res[2];
      );
    );
  );

  if(k15 != 3,
    error(Str("Nombre inattendu de caractères primitifs mod 15: ", k15));
  );

  return(V_values);
};

compute_Veff(T_max, csq) =
{
  my(V_values, num, den, V_eff, ratio);

  V_values = compute_V_values(T_max);
  num = sum(k = 1, 8, csq[k] * V_values[k]);
  den = sum(k = 1, 8, csq[k]);
  V_eff = num / den;
  ratio = 7.0 * V_eff;

  return([V_values, num, den, V_eff, ratio]);
};

main() =
{
  my(csq, Ts, csvfile, out, V_values, num, den, V_eff, ratio);

  print("══════════════════════════════════════");
  print("  V_eff — Scan multi-résolution");
  print("══════════════════════════════════════");
  print("");

  \\ |c_chi|^2 pour TC = {1,11,29}
  csq = [9, 1, 1, 1, 9, 1, 1, 1];

  \\ Liste des coupures à tester
  Ts = [100, 200, 500, 1000, 2000];

  \\ Export CSV
  csvfile = "pari/veff_scan.csv";
  write(csvfile, "T_max,V_eff,ratio_vers_1sur7,delta,delta_abs,time_ms,stack_bytes");

  print("Tableau de convergence");
  print("T_max        V_eff                          ratio=7*V_eff                delta                     temps");
  print("------------------------------------------------------------------------------------------------------------");

  for(i = 1, #Ts,
    my(t0 = getwalltime(), used_before = getstack());

    out = compute_Veff(Ts[i], csq);
    V_values = out[1];
    num = out[2];
    den = out[3];
    V_eff = out[4];
    ratio = out[5];

    my(dt = getwalltime() - t0, used_after = getstack());

    print(Ts[i], "    ", V_eff, "    ", ratio, "    ", ratio - 1.0,
          "    ", strtime(dt));

    write(csvfile,
      Str(Ts[i], ",", V_eff, ",", ratio, ",", ratio - 1.0, ",", abs(ratio - 1.0), ",", dt, ",", used_after)
    );
  );

  print("");
  print("CSV écrit dans : ", csvfile);
  print("");
  print("Lecture :");
  print("- ratio -> 1  : convergence vers 1/7");
  print("- ratio < 1 stable : sous-isotropie persistante");
  print("- ratio oscillant : convergence plus lente / structure plus fine");
};

main();
