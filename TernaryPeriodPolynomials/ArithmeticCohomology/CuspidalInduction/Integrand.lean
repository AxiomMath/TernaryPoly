module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.FaceCanonical

@[expose] public section


/-!
# The triangle integrand of the cup form

Formalized by Claude Sonnet 5.5.

`cupForm` is the sum over representative triangles `y` of the integrand `integ`.  The integrand is unchanged by adding constants to the
cusp functions (the Farey differential sums to zero around a triangle), by pulling back along `γ ∈ SL₂`, and, for twisted cusp functions and an
invariant pairing, is invariant under the translations `y ↦ γ y` of the group.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspidalInduction

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open scoped Classical

section Integrand

variable {A A' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']

/-- The integrand of the cup form at the triangle `y`. -/
def integ (ε : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ) (Φ : RationalLine2 → A) (Φ' : RationalLine2 → A') (y : Tri) : ℂ :=
  ∑ p ∈ nbF y, (ε (Φ (head p)) (Φ' (tail p)) - ε (Φ (tail p)) (Φ' (head p)))

theorem cupForm_eq_sum {N : ℕ} (hN : 3 ≤ N) {ρ : Representation ℂ (gammaNGL N) A} {ρ' : Representation ℂ (gammaNGL N) A'}
    (C : Coupling ρ ρ') (Φ : RationalLine2 → A) (Φ' : RationalLine2 → A') :
    cupForm hN C Φ Φ' = ∑ y ∈ (gammaNFareyData hN).RT.R, integ C.e Φ Φ' y := rfl

/-- Adding constants to the cusp functions does not change the integrand. -/
theorem integ_add_const (ε : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ) (Φ : RationalLine2 → A) (Φ' : RationalLine2 → A') (κ : A) (κ' : A')
    (y : Tri) : integ ε (fun c => Φ c + κ) (fun c => Φ' c + κ') y = integ ε Φ Φ' y := by
  unfold integ
  have key : ∀ p : OTE, (ε (Φ (head p) + κ) (Φ' (tail p) + κ') - ε (Φ (tail p) + κ) (Φ' (head p) + κ')) =
      (ε (Φ (head p)) (Φ' (tail p)) - ε (Φ (tail p)) (Φ' (head p))) + ε (dfun Φ p) κ' - ε κ (dfun Φ' p) := by
    intro p
    simp only [dfun, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    ring
  rw [Finset.sum_congr rfl (fun p _ => key p), Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 : ∑ p ∈ nbF y, ε (dfun Φ p) κ' = 0 := by
    rw [← LinearMap.sum_apply, ← map_sum, sum_dfun_nbF, map_zero, LinearMap.zero_apply]
  have h2 : ∑ p ∈ nbF y, ε κ (dfun Φ' p) = 0 := by
    rw [← map_sum, sum_dfun_nbF, map_zero]
  rw [h1, h2, add_zero, sub_zero]

/-- Pulling back along an `SL₂` element moves the triangle. -/
theorem integ_comp (ε : A →ₗ[ℂ] A' →ₗ[ℂ] ℂ) (Φ : RationalLine2 → A) (Φ' : RationalLine2 → A') {γ : IntegralGL}
    (hγ : IsSL γ) (y : Tri) :
    integ ε (fun c => Φ (γ • c)) (fun c => Φ' (γ • c)) y = integ ε Φ Φ' (γ • y) := by
  unfold integ
  rw [nbF_smul, Finset.sum_image (fun a _ b _ h => MulAction.injective γ h)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [head_smul hγ, tail_smul hγ]

end Integrand

end TernaryPeriodPolynomials.Argument.CuspidalInduction
