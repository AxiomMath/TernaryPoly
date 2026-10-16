module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs

@[expose] public section





/-!
Degree-eight relation `X_i^8 + d4 X_i^4 + d6 X_i^2 + d7 X_i = 0` satisfied by each variable
`X i` over `TernaryPoly.CharTwoNorm.Poly`. This is the characteristic-two Dickson invariant
relation (paper route (ii) for Lemma 5.3's algebraic-independence conjunct): it is the
specialization at `T := X i` of the classical product identity
`∏_{v ∈ 𝔽₂³} (T + v·x) = T^8 + d4 T^4 + d6 T^2 + d7 T`.

We avoid expanding the full 8-factor product by instead using the elementary cubic relation
`X i ^ 3 + a * X i ^ 2 + b * X i + c = 0` (Vieta, since `a, b, c` are literally the elementary
symmetric polynomials of `X 0, X 1, X 2`), proved for `i = 0` by a single `ring` call, then
transported to all `i` by the already-established invariance of `a, b, c, d4, d6, d7` under
`MvPolynomial.rename` of a permutation.
-/

open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

private theorem ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly) = ((n % 2 : ℕ) : Poly) :=
  CharP.cast_eq_mod Poly 2 n

/-- Vieta's relation: `X 0` is a root of `T^3 + aT^2 + bT + c`. -/
theorem cubic_relation_zero :
    (X 0 : Poly) ^ 3 + a * (X 0) ^ 2 + b * (X 0) + c = 0 := by
  simp only [a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

/-- The degree-eight relation at `X 0`. -/
theorem pow8_relation_zero :
    (X 0 : Poly) ^ 8 + d4 * (X 0) ^ 4 + d6 * (X 0) ^ 2 + d7 * (X 0) = 0 := by
  simp only [d4, d6, d7, cplus, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

/-- The degree-eight relation holds at every variable `X i`, transported from `X 0` by the
coordinate permutation swapping `0` and `i`. -/
theorem pow8_relation (i : Fin 3) :
    (X i : Poly) ^ 8 + d4 * (X i) ^ 4 + d6 * (X i) ^ 2 + d7 * (X i) = 0 := by
  have hd4 : rename (Equiv.swap (0 : Fin 3) i) d4 = d4 := by
    simpa [invariant] using rename_invariant (Equiv.swap (0 : Fin 3) i) 0
  have hd6 : rename (Equiv.swap (0 : Fin 3) i) d6 = d6 := by
    simpa [invariant] using rename_invariant (Equiv.swap (0 : Fin 3) i) 1
  have hd7 : rename (Equiv.swap (0 : Fin 3) i) d7 = d7 := by
    simpa [invariant] using rename_invariant (Equiv.swap (0 : Fin 3) i) 2
  have hX : rename (Equiv.swap (0 : Fin 3) i) (X 0 : Poly) = (X i : Poly) := by
    simp [rename_X, Equiv.swap_apply_left]
  have h := congrArg
    (⇑(rename (Equiv.swap (0 : Fin 3) i) : Poly →ₐ[ZMod 2] Poly)) pow8_relation_zero
  simpa [map_add, map_mul, map_pow, hd4, hd6, hd7, hX] using h

end TernaryPeriodPolynomials.Argument.CharTwoKernel
