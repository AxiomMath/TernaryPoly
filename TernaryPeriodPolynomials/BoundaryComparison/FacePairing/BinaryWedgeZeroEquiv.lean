module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InvariantCocycles

@[expose] public section


/-!
# `binaryPairWedge` is a linear equivalence at degree `0`

At every degree, `binaryPairWedge degree (binaryEulerPair degree polynomial) = polynomial`
(`binaryPairWedge_euler`, already in the library, fully degree-generic). This is only a
*one-sided* inverse in general. At degree `0` specifically it is genuinely two-sided: a degree-`0`
binary form is a constant (`binaryHomogeneousPoly_zero_eq_C`), so both partial derivatives
appearing in `binaryEulerPair` kill the "other" summand outright (no product-rule cross terms,
unlike at positive degree), leaving `binaryEulerPair 0 (binaryPairWedge 0 pair) = pair` exactly.

Combined with the (always available) one-sided inverse this makes `binaryPairWedge 0` bijective,
hence (after bundling it as a genuine `ℂ`-linear map, which the library only does as an additive
map `wedgeH`) a `LinearEquiv`.
-/

noncomputable section

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- Every degree-`0` *binary* homogeneous polynomial is the constant polynomial on its own
constant coefficient (binary analogue of `homogeneousPoly_zero_eq_C`). -/
theorem binaryHomogeneousPoly_zero_eq_C (f : Binary.HomogeneousPoly 0) :
    f.val = C (f.val.coeff 0) := by
  have h1 : MvPolynomial.homogeneousComponent 0 f.val = f.val := by
    have h := MvPolynomial.homogeneousComponent_of_mem (n := 0) (m := 0) f.2
    simpa using h
  rw [MvPolynomial.homogeneousComponent_zero] at h1
  exact h1.symm

/-- Differentiating a degree-`0` binary form (a constant) is zero. -/
theorem binaryHomogeneousPoly_zero_pderiv (f : Binary.HomogeneousPoly 0) (i : Fin 2) :
    pderiv i f.val = 0 := by
  rw [binaryHomogeneousPoly_zero_eq_C f]
  exact pderiv_C

theorem binaryPairWedgeZero_add
    (pair1 pair2 : Binary.HomogeneousPoly 0 × Binary.HomogeneousPoly 0) :
    binaryPairWedge 0 (pair1 + pair2) = binaryPairWedge 0 pair1 + binaryPairWedge 0 pair2 := by
  apply Subtype.ext
  simp only [binaryPairWedge, Prod.fst_add, Prod.snd_add, Submodule.coe_add, mul_add]
  ring

theorem binaryPairWedgeZero_smul (c : ℂ)
    (pair : Binary.HomogeneousPoly 0 × Binary.HomogeneousPoly 0) :
    binaryPairWedge 0 (c • pair) = c • binaryPairWedge 0 pair := by
  apply Subtype.ext
  simp only [binaryPairWedge, Prod.smul_fst, Prod.smul_snd, SetLike.val_smul]
  rw [smul_sub, mul_smul_comm, mul_smul_comm]

/-- Bundled `ℂ`-linear map version of `binaryPairWedge 0` (the library only bundles
`binaryPairWedge` additively, as `wedgeH`). -/
def binaryPairWedgeZeroLinear :
    (Binary.HomogeneousPoly 0 × Binary.HomogeneousPoly 0) →ₗ[ℂ] Binary.HomogeneousPoly 1 where
  toFun := binaryPairWedge 0
  map_add' := binaryPairWedgeZero_add
  map_smul' := binaryPairWedgeZero_smul

/-- **`binaryEulerPair 0` undoes `binaryPairWedge 0`.** The converse direction of the
already-proven `binaryPairWedge_euler`, special to degree `0`: differentiating a constant is
zero, so neither partial derivative sees the "other" summand of the wedge formula. -/
theorem binaryEulerPair_binaryPairWedge_zero
    (pair : Binary.HomogeneousPoly 0 × Binary.HomogeneousPoly 0) :
    binaryEulerPair 0 (binaryPairWedge 0 pair) = pair := by
  obtain ⟨a, b⟩ := pair
  have hwedge : (binaryPairWedge 0 (a, b)).val = X 0 * b.val - X 1 * a.val := rfl
  have pderiv1 : pderiv 1 (binaryPairWedge 0 (a, b)).val = -a.val := by
    rw [hwedge]
    simp [binaryHomogeneousPoly_zero_pderiv a 1, binaryHomogeneousPoly_zero_pderiv b 1]
  have pderiv0 : pderiv 0 (binaryPairWedge 0 (a, b)).val = b.val := by
    rw [hwedge]
    simp [binaryHomogeneousPoly_zero_pderiv a 0, binaryHomogeneousPoly_zero_pderiv b 0]
  apply Prod.ext
  · apply Subtype.ext
    simp only [binaryEulerPair, SetLike.val_smul, pderiv1]
    simp
  · apply Subtype.ext
    simp only [binaryEulerPair, SetLike.val_smul, pderiv0]
    simp

theorem binaryPairWedgeZero_bijective : Function.Bijective (binaryPairWedge 0) :=
  ⟨Function.LeftInverse.injective binaryEulerPair_binaryPairWedge_zero,
    Function.RightInverse.surjective (binaryPairWedge_euler 0)⟩

/-- **`binaryPairWedge` at degree `0` is a linear equivalence.** -/
def binaryPairWedgeZeroEquiv :
    (Binary.HomogeneousPoly 0 × Binary.HomogeneousPoly 0) ≃ₗ[ℂ] Binary.HomogeneousPoly 1 :=
  LinearEquiv.ofBijective binaryPairWedgeZeroLinear binaryPairWedgeZero_bijective

end TernaryPeriodPolynomials.Argument.FacePairing
