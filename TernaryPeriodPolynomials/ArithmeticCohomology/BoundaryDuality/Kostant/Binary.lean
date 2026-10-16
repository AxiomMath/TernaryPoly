module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.Apolar
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BinaryPairing

@[expose] public section


/-!
# The apolar pairing of binary forms and the classical invariant pairing

The apolar pairing `⟨x^i y^(N-i), x^j y^(N-j)⟩ = δ_{ij} i! (N-i)!` on binary forms of degree `N`
and the classical `SL₂`-invariant pairing `binaryPairing N` (`⟨x^i y^(N-i), x^j y^(N-j)⟩ =
δ_{i+j,N} (-1)^i / C(N,i)`) differ by the rotation `(x, y) ↦ (-y, x)`:

  `binApolar N f g = N! · binaryPairing N f (g(-y, x))`     (`binApolar_eq_binaryPairing`).

Together with `KostantGoodLine.kostantValue_eq` this expresses the Kostant pairing of the good line
as a nonzero constant multiple `(n+1)!` of `binaryPairing (n+1)` composed with the explicit rotation
`binarySwap` of the identity-plane coordinate.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open MvPolynomial GeneralEisenstein
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

/-- The matrix `[[0, -1], [1, 0]]` of the rotation `(x, y) ↦ (-y, x)` of the variables. -/
def swapMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

theorem linearForm_swap_zero : Binary.linearForm swapMatrix 0 = -(X 1 : Binary.Poly) := by
  simp [Binary.linearForm, swapMatrix, Fin.sum_univ_two]

theorem linearForm_swap_one : Binary.linearForm swapMatrix 1 = (X 0 : Binary.Poly) := by
  simp [Binary.linearForm, swapMatrix, Fin.sum_univ_two]

/-- The rotation `g(x, y) ↦ g(-y, x)` of binary forms of degree `N`. -/
def binarySwap (N : ℕ) : Binary.HomogeneousPoly N →ₗ[ℂ] Binary.HomogeneousPoly N :=
  (Binary.substitute swapMatrix).toLinearMap.restrict fun _ hf =>
    (mem_homogeneousSubmodule N _).mpr
      (Binary.substitute_homogeneous swapMatrix ((mem_homogeneousSubmodule N _).mp hf))

/-- The underlying polynomial of the rotation. -/
@[simp] theorem binarySwap_coe (N : ℕ) (g : Binary.HomogeneousPoly N) :
    ((binarySwap N g : Binary.HomogeneousPoly N) : Binary.Poly) =
      Binary.substitute swapMatrix g.val := rfl

/-- The rotation of a monomial: `(x^j y^(N-j))(-y, x) = (-1)^j x^(N-j) y^j`. -/
theorem substitute_swap_xyPow (N j : ℕ) :
    Binary.substitute swapMatrix (BinaryPairing.xyPow N j) =
      (-1 : ℂ) ^ j • BinaryPairing.xyPowD N j := by
  have hneg : (-(X 1 : Binary.Poly)) ^ j = C ((-1 : ℂ) ^ j) * X 1 ^ j := by
    rw [neg_pow (X 1 : Binary.Poly) j, map_pow, map_neg, map_one]
  simp only [BinaryPairing.xyPow, BinaryPairing.xyPowD]
  rw [BinaryPairing.monomial_mon, BinaryPairing.monomial_mon, map_mul, map_pow, map_pow,
    Binary.substitute_X, Binary.substitute_X, linearForm_swap_zero, linearForm_swap_one, hneg,
    smul_eq_C_mul]
  ring

/-- The lift of a binary monomial to the first two ternary variables. -/
theorem lift_xyPow (N j : ℕ) :
    binaryPolynomialLift (BinaryPairing.xyPow N j) =
      monomial (Finsupp.single 0 j + Finsupp.single 1 (N - j)) (1 : ℂ) := by
  have h0 : binaryPolynomialLift (X (0 : Fin 2)) = (X (0 : Fin 3) : Poly) := by
    simp [binaryPolynomialLift]
  have h1 : binaryPolynomialLift (X (1 : Fin 2)) = (X (1 : Fin 3) : Poly) := by
    simp [binaryPolynomialLift]
  simp only [BinaryPairing.xyPow]
  rw [BinaryPairing.monomial_mon, map_mul, map_pow, map_pow, h0, h1, X_pow_eq_monomial,
    X_pow_eq_monomial, monomial_mul_monomial, mul_one]

/-- The apolar pairing of two monomials. -/
theorem apolar_xyPow (N i j : ℕ) :
    apolarPoly (binaryPolynomialLift (BinaryPairing.xyPow N i))
        (binaryPolynomialLift (BinaryPairing.xyPow N j)) =
      if i = j then (i.factorial : ℂ) * ((N - i).factorial : ℂ) else 0 := by
  have hw : apolarWeight (Finsupp.single (0 : Fin 3) i + Finsupp.single (1 : Fin 3) (N - i)) =
      (i.factorial : ℂ) * ((N - i).factorial : ℂ) := by
    simp [apolarWeight, Fin.prod_univ_three, Finsupp.single_apply]
  rw [lift_xyPow, lift_xyPow, apolarPoly_monomial, hw, mul_one, coeff_monomial]
  by_cases h : i = j
  · subst h
    simp
  · have hne : ¬ (Finsupp.single (0 : Fin 3) j + Finsupp.single (1 : Fin 3) (N - j) =
        Finsupp.single (0 : Fin 3) i + Finsupp.single (1 : Fin 3) (N - i)) := by
      intro heq
      have h0 := DFunLike.congr_fun heq 0
      simp at h0
      exact h h0.symm
    rw [ite_eq_right hne, ite_eq_right h, mul_zero]

/-- **The pairings on the monomial basis.**  For `i, j ≤ N`,
`⟨x^i y^(N-i), x^j y^(N-j)⟩_apolar = N! · ⟨x^i y^(N-i), (x^j y^(N-j))(-y, x)⟩_{SL₂}`. -/
theorem kostant_basis (N i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    apolarPoly (binaryPolynomialLift (BinaryPairing.xyPow N i))
        (binaryPolynomialLift (BinaryPairing.xyPow N j)) =
      (N.factorial : ℂ) * BinaryPairing.binForm N (BinaryPairing.xyPow N i)
        (Binary.substitute swapMatrix (BinaryPairing.xyPow N j)) := by
  rw [apolar_xyPow N i j, substitute_swap_xyPow N j, map_smul,
    BinaryPairing.binForm_right_mono hj, smul_eq_mul]
  simp only [BinaryPairing.xyPow, coeff_monomial]
  by_cases h : i = j
  · subst h
    have hC : ((N.choose i : ℕ) : ℂ) * (i.factorial : ℂ) * ((N - i).factorial : ℂ) =
        (N.factorial : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
    have hne : ((N.choose i : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hi).ne'
    have hsq : ((-1 : ℂ) ^ i) * ((-1 : ℂ) ^ i) = 1 := by
      rw [← mul_pow]
      norm_num
    have key : (N.factorial : ℂ) * ((-1 : ℂ) ^ i * (BinaryPairing.pairCoef N i * 1)) =
        (i.factorial : ℂ) * ((N - i).factorial : ℂ) := by
      unfold BinaryPairing.pairCoef
      rw [← hC]
      have e : ((N.choose i : ℕ) : ℂ) * (i.factorial : ℂ) * ((N - i).factorial : ℂ) *
          ((-1 : ℂ) ^ i * ((-1 : ℂ) ^ i * ((N.choose i : ℕ) : ℂ)⁻¹ * 1)) =
          (((N.choose i : ℕ) : ℂ) * ((N.choose i : ℕ) : ℂ)⁻¹) *
            (((-1 : ℂ) ^ i) * ((-1 : ℂ) ^ i)) * ((i.factorial : ℂ) * ((N - i).factorial : ℂ)) := by
        ring
      rw [e, mul_inv_cancel₀ hne, hsq]
      ring
    rw [ite_eq_left rfl, ite_eq_left rfl]
    exact key.symm
  · have hne : ¬ (BinaryPairing.mon i (N - i) = BinaryPairing.mon j (N - j)) := by
      intro heq
      exact h (BinaryPairing.mon_inj heq).1
    rw [ite_eq_right h, ite_eq_right hne]
    simp

/-- **The apolar pairing of binary forms is `N!` times the invariant pairing against the rotation.** -/
theorem binApolar_eq_binaryPairing (N : ℕ) (f g : Binary.HomogeneousPoly N) :
    binApolar N f g =
      (N.factorial : ℂ) * BinaryPairing.binaryPairing N f (binarySwap N g) := by
  have key := BinaryPairing.eq_of_basis N
    (apolarPoly.compl₁₂ binaryPolynomialLift.toLinearMap binaryPolynomialLift.toLinearMap)
    ((N.factorial : ℂ) •
      (BinaryPairing.binForm N).compl₂ (Binary.substitute swapMatrix).toLinearMap)
    (fun i hi j hj => by
      simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, LinearMap.compl₂_apply,
        AlgHom.toLinearMap_apply, smul_eq_mul]
      exact kostant_basis N i j hi hj)
    ((mem_homogeneousSubmodule N _).mp f.2) ((mem_homogeneousSubmodule N _).mp g.2)
  exact key

/-- **Perfectness of the invariant pairing against the rotation.** -/
theorem binaryPairing_swap_left_eq_zero (N : ℕ) {f : Binary.HomogeneousPoly N}
    (h : ∀ g, BinaryPairing.binaryPairing N f (binarySwap N g) = 0) : f = 0 := by
  apply binApolar_left_eq_zero
  intro g
  rw [binApolar_eq_binaryPairing, h g, mul_zero]

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
