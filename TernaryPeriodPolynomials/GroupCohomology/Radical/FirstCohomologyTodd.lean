module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantMatrices
public import TernaryPeriodPolynomials.GroupCohomology.Radical.ToddExact
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Homogeneous
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.RadicalFirstCohomologyTodd
open RadicalCoinvariantAlgebra

/-- The finite Todd operator as a rational linear map on actual ternary coefficients. -/
def firstToddLinear (u : MvPolynomial (Fin 2) ℚ) : Poly →ₗ[ℚ] Poly :=
  (finSuccEquiv ℚ 2).symm.toLinearMap.comp
    (((todd u).restrictScalars ℚ).comp (finSuccEquiv ℚ 2).toLinearMap)

@[simp] theorem firstToddLinear_apply (u : MvPolynomial (Fin 2) ℚ) (f : Poly) :
    firstToddLinear u f=ternaryTodd u f := rfl

/-- A linear coordinate parameter preserves the exact homogeneous coefficient space. -/
def firstTodd (n : ℕ) (j : Fin 2) : H n →ₗ[ℚ] H n where
  toFun f := ⟨ternaryTodd (X j) f,ternaryTodd_homogeneous f.property (isHomogeneous_X ℚ j)⟩
  map_add' f g := Subtype.ext ((firstToddLinear (X j)).map_add f g)
  map_smul' r f := Subtype.ext ((firstToddLinear (X j)).map_smul r f)

@[simp] theorem firstTodd_coe (n : ℕ) (j : Fin 2) (f : H n) :
    (firstTodd n j f : Poly)=ternaryTodd (X j) f := rfl

theorem firstTodd_injective (n : ℕ) (j : Fin 2) : Function.Injective (firstTodd n j) := by
  intro f g h
  apply Subtype.ext
  exact ternaryTodd_injective (X j) (congrArg Subtype.val h)

/-- The explicit finite Todd map is invertible on every exact homogeneous degree. -/
def firstToddEquiv (n : ℕ) (j : Fin 2) : H n ≃ₗ[ℚ] H n := by
  letI : Module.Finite ℚ (H n) := Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 3) ℚ n)
  exact LinearEquiv.ofInjectiveEndo (firstTodd n j) (firstTodd_injective n j)

@[simp] theorem firstToddEquiv_coe (n : ℕ) (j : Fin 2) (f : H n) :
    (firstToddEquiv n j f : Poly)=ternaryTodd (X j) f := rfl

/-- Exact Todd conversion of each actual line-radical lattice difference. -/
theorem firstTodd_difference (n : ℕ) (j : Fin 2) (f : H n) :
    (firstToddEquiv n j (difference n 0 j.succ f) : Poly)=
      -(X j.succ)*pderiv 0 (f : Poly) := by
  apply (finSuccEquiv ℚ 2).injective
  change finSuccEquiv ℚ 2 (ternaryTodd (X j) (shear 0 j.succ f-f))=_
  simp only [ternaryTodd,AlgEquiv.apply_symm_apply,map_sub,finSuccEquiv_shear,
    map_mul,map_neg,finSuccEquiv_X_succ,finSuccEquiv_pderiv_zero]
  simpa only [map_sub,Polynomial.smul_eq_C_mul,map_neg] using
    todd_difference (X j) (finSuccEquiv ℚ 2 (f : Poly))

/-- The two finite Todd maps for the line radical commute. -/
theorem firstTodd_commute (n : ℕ) (i j : Fin 2) (f : H n) :
    firstToddEquiv n i (firstToddEquiv n j f)=firstToddEquiv n j (firstToddEquiv n i f) := by
  apply Subtype.ext
  apply (finSuccEquiv ℚ 2).injective
  simp only [firstToddEquiv_coe,ternaryTodd,AlgEquiv.apply_symm_apply]
  exact todd_commute (X i) (X j) (finSuccEquiv ℚ 2 (f : Poly))

end TernaryPoly.RadicalFirstCohomologyTodd
