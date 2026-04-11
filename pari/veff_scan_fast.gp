\\ pari/veff_scan_fast.gp
\\ Scan rapide de V_eff :
\\ 1) on calcule les zeros une seule fois au T_max final
\\ 2) on recycle ces zeros pour tous les T intermediaires
\\
\\ Lancement conseille :
\\ gp -s 256000000 -D parisizemax=4000000000 < pari/veff_scan_fast.gp

\\ Pour accelerer encore un scan exploratoire, tu peux essayer 28 ou 19
default(realprecision, 28);

scan_sums_from_zeros(z, Ts) =
{
  my(vals = vector(#Ts), s = 0.0, j = 1);

  for(i = 1, #Ts,
    while(j <= #z && z[j] <= Ts[i],
      s += 2.0 / (0.25 + z[j]^2);
      j++;
    );
    vals[i] = s;
  );

  return(vals);
};

build_zero_scans(Ts) =
{
  my(Tmax = Ts[#Ts]);
  my(specs, names, zero_scans, zero_counts, char_times, t0, L, z);

  \\ Ordre documentaire :
  \\ 1: chi(0,0) cond=1
  \\ 2: chi(0,1) cond=5 label 2
  \\ 3: chi(0,2) cond=5 label 3
  \\ 4: chi(0,3) cond=5 label 4
  \\ 5: chi(1,0) cond=3 label 2
  \\ 6: chi(1,1) cond=15 label 2
  \\ 7: chi(1,2) cond=15 label 8
  \\ 8: chi(1,3) cond=15 label 14

  specs = [
    1,
    Mod(2, 5),
    Mod(3, 5),
    Mod(4, 5),
    Mod(2, 3),
    Mod(2, 15),
    Mod(8, 15),
    Mod(14, 15)
  ];

  names = [
    "chi(0,0)",
    "chi(0,1)",
    "chi(0,2)",
    "chi(0,3)",
    "chi(1,0)",
    "chi(1,1)",
    "chi(1,2)",
    "chi(1,3)"
  ];

  zero_scans = vector(8);
  zero_counts = vector(8);
  char_times = vector(8);

  print("Precalcul des zeros jusqu'a T_max final = ", Tmax);
  print("------------------------------------------------------------");

  for(k = 1, 8,
    t0 = getwalltime();
    L = lfuninit(specs[k], [Tmax]);
    z = lfunzeros(L, Tmax);
    zero_scans[k] = scan_sums_from_zeros(z, Ts);
    zero_counts[k] = #z;
    char_times[k] = getwalltime() - t0;

    print(names[k], " : ", #z, " zeros   temps = ", strtime(char_times[k]));
  );

  return([zero_scans, zero_counts, char_times]);
};

main() =
{
  my(csq, Ts, csvfile, out, zero_scans, zero_counts, char_times);
  my(den, num, V_eff, ratio, delta, total_pre_ms);

  csq = [9, 1, 1, 1, 9, 1, 1, 1];

  \\ Ajuste ici
  Ts = [100, 200, 500, 1000, 2000, 3000, 4000, 5000];

  csvfile = "pari/veff_scan_fast.csv";

  print("══════════════════════════════════════");
  print("  V_eff — Scan rapide memoise");
  print("══════════════════════════════════════");
  print("");

  out = build_zero_scans(Ts);
  zero_scans = out[1];
  zero_counts = out[2];
  char_times = out[3];

  total_pre_ms = sum(k = 1, 8, char_times[k]);
  den = sum(k = 1, 8, csq[k]);

  print("");
  print("Temps total precalcul zeros = ", strtime(total_pre_ms));
  print("");

  write(csvfile, "T_max,V_eff,ratio_vers_1sur7,delta,delta_abs");

  print("Tableau de convergence");
  print("T_max        V_eff                          ratio=7*V_eff                delta                     temps");
  print("------------------------------------------------------------------------------------------------------------");

  for(i = 1, #Ts,
    my(t0 = getwalltime(), used_before = getstack());

    num = sum(k = 1, 8, csq[k] * zero_scans[k][i]);
    V_eff = num / den;
    ratio = 7.0 * V_eff;
    delta = ratio - 1.0;

    my(dt = getwalltime() - t0, used_after = getstack());

    print(Ts[i], "    ", V_eff, "    ", ratio, "    ", delta,
          "    ", strtime(dt));
    write(csvfile,
      Str(Ts[i], ",", V_eff, ",", ratio, ",", delta, ",", abs(delta), dt, ",", used_after)
    );
  );

  print("");
  print("CSV ecrit dans : ", csvfile);
};

main();