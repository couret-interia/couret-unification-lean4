\\ V_eff test — Programme Couret-Unification
\\ Usage: gp < pari/veff_high_res.gp

V_from_L(L, T) =
{
  my(z, s = 0.0);
  z = lfunzeros(L, T);
  for(j = 1, #z, s += 2.0 / (0.25 + z[j]^2));
  return([#z, s]);
};

main() =
{
  my(conductors, csq, T_max, V_values, res, G3, G5, G15, idx, k15, G0, chi0);

  print("══════════════════════════════════════");
  print("  V_eff — Test haute résolution");
  print("══════════════════════════════════════");

  conductors = [1, 5, 5, 5, 3, 15, 15, 15];
  csq = [9, 1, 1, 1, 9, 1, 1, 1];

  T_max = 500;
  V_values = vector(8);

  print("T_max = ", T_max);
  print("");

  \\ 1) caractère trivial : zeta
  res = V_from_L(1, T_max);
  V_values[1] = res[2];
  print("chi(0,0) cond=1  : ", res[1], " zeros, V = ", res[2]);

  \\ 2) caractère non trivial mod 3
  \\ On utilise ici la notation de Conrey Mod(2,3)
  res = V_from_L(Mod(2, 3), T_max);
  V_values[5] = res[2];
  print("chi(1,0) cond=3  : ", res[1], " zeros, V = ", res[2]);

  \\ 3) caractères non triviaux mod 5 : labels 2,3,4
  idx = 2;
  for(m = 2, 4,
    res = V_from_L(Mod(m, 5), T_max);
    V_values[idx] = res[2];
    print("chi(0,", idx - 1, ") cond=5  : label ", m, ", ", res[1], " zeros, V = ", res[2]);
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
        print("chi(1,", k15, ") cond=15 : label ", m, ", ", res[1], " zeros, V = ", res[2]);
      );
    );
  );

  if(k15 != 3,
    error(Str("Nombre inattendu de caractères primitifs mod 15: ", k15));
  );

  print("");
  print("══ V(chi) complet ══");
  for(k = 1, 8, print("V[", k, "] = ", V_values[k]));

  my(num, den, V_eff);
  num = sum(k = 1, 8, csq[k] * V_values[k]);
  den = sum(k = 1, 8, csq[k]);
  V_eff = num / den;

  print("");
  print("══ RÉSULTAT ══");
  print("sum |c_chi|^2 = ", den);
  print("sum |c_chi|^2 V(chi) = ", num);
  print("V_eff = ", V_eff);
  print("Cible 1/7 = ", 1.0 / 7);
  print("Ratio V_eff / (1/7) = ", 7.0 * V_eff);
  print("");

  if(abs(7.0 * V_eff - 1.0) < 0.1,
    print("✅ Ratio proche de 1 — isotropie possible"),
    print("❌ Ratio ≠ 1 — isotropie non observée à T_max = ", T_max)
  );
};

main();