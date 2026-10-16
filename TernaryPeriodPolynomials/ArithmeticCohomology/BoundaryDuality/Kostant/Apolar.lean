module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Apolar
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PolynomialDerivativeKernel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.PolynomialRestriction

@[expose] public section


/-!
# The apolar pairing of binary forms and ternary forms free of the third variable

The Kostant pairing of the good line is, in the binary coordinates of `H¹(ℤ², V)`, the apolar
pairing `⟨f, g⟩ = f(∂) g` of binary forms of degree `N = n + 1`.  This module transports the
ternary apolar pairing of `Duality.Apolar` to binary forms through the lift
`Binary.Poly → Poly` (the forms in the first two variables), and records the three facts used
to compute the coefficient pairing `dualPairing` against forms which do not involve `X₂`.

* `apolarPoly_comm`: symmetry of the apolar pairing.
* `dualPairing_eq_of_pderiv_third_zero`: for `P` with `∂₂ P = 0` the pairing `⟨P, w⟩` only sees
  `w` modulo `X₂` (the level scaling `diag(1, 1, 3)` is invisible there).
* `binApolar`: the apolar pairing on `Sym^N` of two variables, with `binApolar_left_eq_zero` and
  `binApolar_right_eq_zero` (perfectness).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open MvPolynomial GeneralEisenstein
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

/-- The apolar pairing of ternary polynomials is symmetric. -/
theorem apolarPoly_comm (f k : Poly) : apolarPoly f k = apolarPoly k f := by
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [apolarPoly_monomial, apolarPoly_monomial_right]
    ring
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]

/-- The apolar pairing of a form free of `X₂` only sees the other argument modulo `X₂`. -/
theorem apolarPoly_eq_restrict {f : Poly} (hf : pderiv 2 f = 0) (k : Poly) :
    apolarPoly f k = apolarPoly f (binaryPolynomialLift (binaryPolynomialRestrict k)) := by
  obtain ⟨g, hg⟩ := binaryPolynomialRestrict_difference_dvd k
  have h0 : apolarPoly f (k - binaryPolynomialLift (binaryPolynomialRestrict k)) = 0 := by
    rw [hg, apolarPoly_comm, apolarPoly_X_mul, hf, map_zero]
  rw [map_sub] at h0
  exact sub_eq_zero.mp h0

/-- Scaling the third variable does not change the restriction to `X₂ = 0`. -/
theorem binaryPolynomialRestrict_substitute_scale (k : Poly) :
    binaryPolynomialRestrict (substitute complexLevelScale k) = binaryPolynomialRestrict k := by
  have h : binaryPolynomialRestrict.comp (substitute complexLevelScale) =
      binaryPolynomialRestrict := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, substitute_X, linearForm, complexLevelScale_eq]
    fin_cases i <;> simp [binaryPolynomialRestrict, Fin.sum_univ_three, Matrix.diagonal_apply]
  exact congrArg (fun φ : Poly →ₐ[ℂ] Binary.Poly => φ k) h

/-- **The coefficient pairing against a form free of `X₂`.**  For `P` with `∂₂ P = 0`,
`⟨P, w⟩ = ⟨P, w|_{X₂ = 0}⟩_apolar`. -/
theorem dualPairing_eq_of_pderiv_third_zero (n : ℕ) (P w : HomogeneousPoly n)
    (hP : pderiv 2 P.val = 0) :
    dualPairing n P w =
      apolarPoly P.val (binaryPolynomialLift (binaryPolynomialRestrict w.val)) := by
  rw [dualPairing_apply, apolar_apply, homogeneousSubstitute_coe,
    apolarPoly_eq_restrict hP (substitute complexLevelScale w.val),
    binaryPolynomialRestrict_substitute_scale]

/-- The lift of binary polynomials to the first two variables commutes with the derivatives. -/
theorem lift_pderiv_castSucc (i : Fin 2) (f : Binary.Poly) :
    pderiv i.castSucc (binaryPolynomialLift f) = binaryPolynomialLift (pderiv i f) :=
  pderiv_rename (Fin.castSucc_injective 2) i f

/-- The apolar pairing on binary forms of degree `N`, `⟨f, g⟩ = f(∂) g`, defined through the lift
to the first two variables of the ternary apolar pairing. -/
def binApolar (N : ℕ) :
    Binary.HomogeneousPoly N →ₗ[ℂ] Binary.HomogeneousPoly N →ₗ[ℂ] ℂ :=
  apolarPoly.compl₁₂
    (binaryPolynomialLift.toLinearMap ∘ₗ (Binary.HomogeneousPoly N).subtype)
    (binaryPolynomialLift.toLinearMap ∘ₗ (Binary.HomogeneousPoly N).subtype)

/-- Unfolding the binary apolar pairing. -/
theorem binApolar_apply (N : ℕ) (f g : Binary.HomogeneousPoly N) :
    binApolar N f g = apolarPoly (binaryPolynomialLift f.val) (binaryPolynomialLift g.val) := rfl

/-- The binary apolar pairing is symmetric. -/
theorem binApolar_comm (N : ℕ) (f g : Binary.HomogeneousPoly N) :
    binApolar N f g = binApolar N g f := by
  rw [binApolar_apply, binApolar_apply]
  exact apolarPoly_comm _ _

/-- The binary apolar pairing is nondegenerate in its first variable. -/
theorem binApolar_left_eq_zero (N : ℕ) {f : Binary.HomogeneousPoly N}
    (h : ∀ g, binApolar N f g = 0) : f = 0 := by
  apply Subtype.ext
  ext m
  rw [Submodule.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hm
  have hdeg := (mem_homogeneousSubmodule N _).mp f.2 hm
  have hg := h ⟨monomial m 1, (mem_homogeneousSubmodule N _).mpr
    (isWeightedHomogeneous_monomial 1 m 1 hdeg)⟩
  rw [binApolar_apply] at hg
  have hlift : binaryPolynomialLift (monomial m (1 : ℂ)) =
      monomial (Finsupp.mapDomain Fin.castSucc m) 1 := rename_monomial Fin.castSucc m (1 : ℂ)
  have hc : (binaryPolynomialLift f.val).coeff (Finsupp.mapDomain Fin.castSucc m) =
      f.val.coeff m :=
    coeff_rename_mapDomain Fin.castSucc (Fin.castSucc_injective 2) f.val m
  change apolarPoly (binaryPolynomialLift f.val) (binaryPolynomialLift (monomial m 1)) = 0
    at hg
  rw [hlift, apolarPoly_monomial_right, hc, mul_one] at hg
  exact hm ((mul_eq_zero.mp hg).resolve_left (apolarWeight_ne_zero _))

/-- The binary apolar pairing is nondegenerate in its second variable. -/
theorem binApolar_right_eq_zero (N : ℕ) {g : Binary.HomogeneousPoly N}
    (h : ∀ f, binApolar N f g = 0) : g = 0 :=
  binApolar_left_eq_zero N fun f => (binApolar_comm N g f).trans (h f)

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
