#!/bin/bash
# run_all_tests.sh — Pack de tests final Couret-Unification
set -e
mkdir -p outputs
echo "╔══════════════════════════════════════════════════════════╗"
echo "║  TESTS FINAUX — Programme Couret-Unification             ║"
echo "║  Alexandre Couret — Avril 2026                           ║"
echo "╚══════════════════════════════════════════════════════════╝"
TOTAL=0; PASSED=0; FAILED=0
run_test() {
    echo "━━━ $1 ━━━"; TOTAL=$((TOTAL+1))
    if python3 "$2" 2>&1; then PASSED=$((PASSED+1))
    else FAILED=$((FAILED+1)); echo "  ⚠ ÉCHEC"; fi; echo ""
}
echo ""; echo "═══ SOCLE FINI ═══"
run_test "N1 — Noyau fini" test_finite_core.py
run_test "N2 — KLMN" test_klmn_bound.py
echo "═══ TOUR PRIMORIALE ═══"
run_test "N3 — Parseval tower" test_parseval_tower.py
run_test "N4 — Euler defect" test_euler_defect.py
echo "═══ FORMULE EXPLICITE ═══"
run_test "N5 — Guinand-Weil" test_guinand_weil.py
run_test "N6 — σ_k matching" test_sigma_matching.py
echo "═══ RÉSULTATS NÉGATIFS ═══"
run_test "N7 — Routes éliminées" test_negative_results.py
echo "═══ GÉOMÉTRIE CAYLEYENNE ═══"
run_test "N9 — Cayley connexité" test_cayley_connectivity.py
echo "═══ TEST FALSIFIABLE H3 (~2min) ═══"
run_test "N8 — V(χ) channelwise" test_vchi_channels.py
echo "╔══════════════════════════════════════════════════════════╗"
printf "║  Total: %-2d  Pass: %-2d  Fail: %-2d                           ║\n" $TOTAL $PASSED $FAILED
echo "╚══════════════════════════════════════════════════════════╝"
[ $FAILED -eq 0 ] && echo "✓ TOUS LES TESTS PASSENT" || echo "✗ $FAILED ÉCHEC(S)"
exit $FAILED
