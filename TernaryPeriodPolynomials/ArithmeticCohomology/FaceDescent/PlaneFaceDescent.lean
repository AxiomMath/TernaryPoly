module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.FaceActionDescent
public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.PlaneFaceAction

@[expose] public section


/-!
# The descended canonical pairing of the plane face is perfect

Formalized by Claude Sonnet 5.5.

Let `G = bigPlaneStabAt h` be the stabilizer in `SL₃(ℤ)` of the the plane face cusp `h⁻¹ P h` (its Levi image is all of `GL₂(ℤ)`: the determinant and reflection elements are included), acting on the extension `ℤ² → E → Γ(N)` of the cusp (`N ≥ 3`), on the
radical, on the Levi `Γ(N)` and on a coefficient module `ρ̃` of `SL₃(ℤ)`.  `gammaNPAt N h` is a normal subgroup of finite index of `G` acting trivially on the cuspidal groups (`FaceAction.cuspAct_inner`), so the finite covering group is `G ⧸ gammaNPAt N h`.
`planeFace_descends_left/right`: the canonical pairing `facePairingCan` of the cuspidal groups `𝒞(H¹(N_R, ρ))`, `𝒞(H¹(N_R, ρ^*))` is perfect on the `G`-invariants.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceDescent

open TernaryPeriodPolynomials.Argument.FrameInvariance
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N) (h : SL(3, ℤ)) {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ SL(3, ℤ) V)

/-- The elements of the face group of `Γ(N)` act as inner elements. -/
theorem planeFace_inner (k : bigPlaneStabAt h) (hk : k ∈ (gammaNPAt N h).subgroupOf (bigPlaneStabAt h)) :
    ∃ e : gammaNPAt N h, (∀ e', (planeFaceAction N hN h ρ).θ k e' = e * e' * e⁻¹) ∧
      ∀ v, (planeFaceAction N hN h ρ).T k v = (planeGRep ρ N h).ρ e v := by
  refine ⟨⟨k.1, hk⟩, fun e' => Subtype.ext ?_, fun v => rfl⟩
  show (((planeGθ N hN h k) e' : gammaNPAt N h) : SL(3, ℤ)) = k.1 * e'.1 * k.1⁻¹
  exact planeGθ_val N hN h k e'

variable [FiniteDimensional ℂ (planeGRep ρ N h)]

/-- **The descended canonical pairing of the plane face is perfect (left kernel).**  A class of the `G`-invariants of `𝒞(H¹(N_R, ρ))` which pairs to zero with every `G`-invariant class of `𝒞(H¹(N_R, ρ^*))` is zero. -/
theorem planeFace_descends_left
    (x : (planeFaceAction N hN h ρ).invariants (faceSplitting N h))
    (hx : ∀ y : (planeFaceAction N hN h ρ).invariantsDual (faceSplitting N h),
      facePairingCan hN (faceSplitting N h) (planeFaceRadicalInput_det N h) (planeGRep ρ N h) x.1 y.1 = 0) : x = 0 := by
  have := gammaNPAt_big_normal N h
  have hfi := gammaNPAt_big_finiteIndex N h hN
  have : Finite (↥(bigPlaneStabAt h) ⧸ (gammaNPAt N h).subgroupOf (bigPlaneStabAt h)) :=
    @Subgroup.finite_quotient_of_finiteIndex _ _ _ hfi
  exact (planeFaceAction N hN h ρ).cusp_descends_left (faceSplitting N h) (planeFaceRadicalInput_det N h) ((gammaNPAt N h).subgroupOf (bigPlaneStabAt h))
    (planeFace_inner N hN h ρ) (planeFaceAction_radDet N hN h ρ) x hx

/-- **Right kernel.** -/
theorem planeFace_descends_right
    (y : (planeFaceAction N hN h ρ).invariantsDual (faceSplitting N h))
    (hy : ∀ x : (planeFaceAction N hN h ρ).invariants (faceSplitting N h),
      facePairingCan hN (faceSplitting N h) (planeFaceRadicalInput_det N h) (planeGRep ρ N h) x.1 y.1 = 0) : y = 0 := by
  have := gammaNPAt_big_normal N h
  have hfi := gammaNPAt_big_finiteIndex N h hN
  have : Finite (↥(bigPlaneStabAt h) ⧸ (gammaNPAt N h).subgroupOf (bigPlaneStabAt h)) :=
    @Subgroup.finite_quotient_of_finiteIndex _ _ _ hfi
  exact (planeFaceAction N hN h ρ).cusp_descends_right (faceSplitting N h) (planeFaceRadicalInput_det N h) ((gammaNPAt N h).subgroupOf (bigPlaneStabAt h))
    (planeFace_inner N hN h ρ) (planeFaceAction_radDet N hN h ρ) y hy

end TernaryPeriodPolynomials.Argument.FaceDescent
