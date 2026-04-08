#!/usr/bin/env python3
"""
Compute spectral moments M₂, M₄, M₆ along the primorial tower.
Tests the conjecture μ_k → δ₁ (Dirac at 1).

If M₄(k)/M₂(k)² → 1, the conjecture is supported.
If M₄(k)/M₂(k)² stays away from 1, the conjecture fails.
"""
import numpy as np
from itertools import product as iprod

TC = [1, 11, 29]

def euler_phi(n):
    """Euler's totient function."""
    result = n
    p = 2
    temp = n
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            result -= result // p
        p += 1
    if temp > 1:
        result -= result // temp
    return result

def multiplicative_group(n):
    """Return list of elements of (ℤ/nℤ)×."""
    from math import gcd
    return [k for k in range(n) if gcd(k, n) == 1]

def discrete_log_table(n):
    """For each prime power factor of n, compute characters."""
    pass

def all_characters_mod_n(n):
    """
    Compute all Dirichlet characters mod n as functions ℤ → ℂ.
    Uses the structure (ℤ/nℤ)× via explicit computation.
    Returns list of functions χ : int → complex.
    """
    G = multiplicative_group(n)
    phi_n = len(G)
    
    # Build character table by DFT on the group
    # For abelian group, characters are indexed by group elements
    # χ_k(g) = exp(2πi · ind(g) · k / ord(g)) via the group structure
    
    # Step 1: find a generator system (may need multiple generators for non-cyclic)
    # For simplicity, compute the full character table numerically
    
    # Map group elements to indices
    g_to_idx = {g: i for i, g in enumerate(G)}
    
    # Multiplication table
    mult_table = np.zeros((phi_n, phi_n), dtype=int)
    for i, gi in enumerate(G):
        for j, gj in enumerate(G):
            mult_table[i, j] = g_to_idx[(gi * gj) % n]
    
    # Find characters by solving χ(g·h) = χ(g)·χ(h)
    # For a finite abelian group, the characters form the dual group
    # We can find them via the structure theorem
    
    # Alternative: use the DFT approach
    # The regular representation decomposes into irreducibles
    # Each character appears with multiplicity 1
    
    # Compute eigenvalues of the regular representation matrices
    # R_g[i,j] = 1 if g·G[i] = G[j], else 0
    
    # For efficiency, use the fact that characters are simultaneous 
    # eigenvectors of all R_g
    
    # Pick a generating element and find its eigenvalues
    # For (ℤ/nℤ)×, we can use the Smith normal form / CRT decomposition
    
    # PRACTICAL APPROACH: enumerate characters via CRT
    # Factor n into prime powers
    def factorize(m):
        factors = {}
        d = 2
        while d * d <= m:
            while m % d == 0:
                factors[d] = factors.get(d, 0) + 1
                m //= d
            d += 1
        if m > 1:
            factors[m] = factors.get(m, 0) + 1
        return factors
    
    factors = factorize(n)
    prime_powers = [p**e for p, e in factors.items()]
    
    # Characters of (ℤ/p^e ℤ)× for each prime power
    def chars_prime_power(pe):
        G_pe = multiplicative_group(pe)
        phi_pe = len(G_pe)
        if phi_pe == 0:
            return [lambda x: 1.0+0j]
        
        # Find a primitive root mod pe
        def find_generator(pe, G_pe, phi_pe):
            for g in G_pe:
                if g <= 1:
                    continue
                order = 1
                val = g
                while val % pe != 1:
                    val = (val * g) % pe
                    order += 1
                if order == phi_pe:
                    return g
            return G_pe[1] if len(G_pe) > 1 else 1
        
        gen = find_generator(pe, G_pe, phi_pe)
        
        # Discrete log table
        dlog = {}
        val = 1
        for k in range(phi_pe):
            dlog[val] = k
            val = (val * gen) % pe
        
        # Characters: χ_j(g) = exp(2πi · j · dlog(g) / phi_pe)
        chars = []
        for j in range(phi_pe):
            def make_char(j_val, pe_val, dlog_val, phi_val):
                def chi(x):
                    x_mod = x % pe_val
                    from math import gcd
                    if gcd(x_mod, pe_val) > 1:
                        return 0.0+0j
                    return np.exp(2j * np.pi * j_val * dlog_val[x_mod] / phi_val)
                return chi
            chars.append(make_char(j, pe, dlog, phi_pe))
        
        return chars
    
    # Get characters for each prime power factor
    char_lists = [chars_prime_power(pe) for pe in prime_powers]
    
    # Combine via CRT: χ(x) = Π χ_pe(x mod pe)
    all_chars = []
    for combo in iprod(*char_lists):
        def make_combined(combo_val, pps):
            def chi(x):
                result = 1.0+0j
                for chi_pe, pe in zip(combo_val, pps):
                    result *= chi_pe(x % pe)
                return result
            return chi
        all_chars.append(make_combined(combo, prime_powers))
    
    return all_chars

def compute_moments(n, tc=TC, max_moment=4):
    """Compute moments M₂, M₄, M₆, M₈ for characters mod n."""
    chars = all_characters_mod_n(n)
    phi_n = len(chars)
    
    # Compute |S(χ)|² for each character
    energies = []
    for chi in chars:
        S = sum(chi(r) for r in tc)
        energies.append(abs(S)**2)
    
    energies = np.array(energies)
    
    # Moments
    moments = {}
    for k in range(1, max_moment + 1):
        M_2k = np.sum(energies**k) / phi_n
        moments[2*k] = M_2k
    
    return phi_n, energies, moments

def main():
    print("=" * 70)
    print("COURET-UNIFICATION — Spectral Moment Computation")
    print("TC = {1, 11, 29}")
    print("=" * 70)
    
    levels = [
        (30,    "L3"),
        (210,   "L4"),
        (2310,  "L5"),
    ]
    
    results = {}
    
    for n, label in levels:
        phi_n, energies, moments = compute_moments(n, max_moment=4)
        results[label] = (phi_n, energies, moments)
        
        M2 = moments[2]
        M4 = moments[4]
        M6 = moments[6]
        M8 = moments[8]
        
        # Normalized ratios (if μ_k → δ₁, these → 1)
        r4 = M4 / M2**2
        r6 = M6 / M2**3
        r8 = M8 / M2**4
        
        print(f"\n{'─'*70}")
        print(f"Level {label} (mod {n}, φ = {phi_n})")
        print(f"{'─'*70}")
        print(f"  M₂  = {M2:.6f}  (should be 3.000)")
        print(f"  M₄  = {M4:.6f}")
        print(f"  M₆  = {M6:.6f}")
        print(f"  M₈  = {M8:.6f}")
        print(f"  ")
        print(f"  M₄/M₂² = {r4:.6f}  (δ₁ target: 1.000)")
        print(f"  M₆/M₂³ = {r6:.6f}  (δ₁ target: 1.000)")
        print(f"  M₈/M₂⁴ = {r8:.6f}  (δ₁ target: 1.000)")
        
        # Spectral histogram
        print(f"  ")
        print(f"  |S(χ)|² distribution:")
        vals, counts = np.unique(np.round(energies, 6), return_counts=True)
        for v, c in zip(vals, counts):
            pct = 100.0 * c / phi_n
            print(f"    |S|² = {v:8.4f}  : {c:4d} chars ({pct:5.1f}%)")
    
    # Convergence analysis
    print(f"\n{'='*70}")
    print(f"CONVERGENCE ANALYSIS: M₄/M₂² along the tower")
    print(f"{'='*70}")
    for label in ["L3", "L4", "L5"]:
        phi_n, _, moments = results[label]
        r = moments[4] / moments[2]**2
        print(f"  {label}: M₄/M₂² = {r:.6f}")
    
    r3 = results["L3"][2][4] / results["L3"][2][2]**2
    r4 = results["L4"][2][4] / results["L4"][2][2]**2
    r5 = results["L5"][2][4] / results["L5"][2][2]**2
    
    if r4 < r3 and r5 < r4:
        print(f"\n  ✓ MONOTONE DECREASE: {r3:.4f} > {r4:.4f} > {r5:.4f}")
        print(f"    Supports μ_k → δ₁ conjecture")
    elif r5 < r3:
        print(f"\n  ~ OVERALL DECREASE: {r3:.4f} → {r5:.4f}")
        print(f"    Partially supports conjecture")
    else:
        print(f"\n  ✗ NO CLEAR DECREASE")
        print(f"    Conjecture may need revision")
    
    print(f"\n  Target (δ₁): M₄/M₂² = 1.000")
    print(f"  Current gap at L5: {abs(r5 - 1.0):.4f}")

if __name__ == "__main__":
    main()
