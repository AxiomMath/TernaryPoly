module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.FaceActionDescent
public import TernaryPeriodPolynomials.ArithmeticCohomology.FaceDescent.LineFaceAction

@[expose] public section


/-!
# The descended canonical pairing of the line face is perfect

Formalized by Claude Sonnet 5.5.

Let `G = bigLineStabAt h` be the stabilizer in `SL₃(ℤ)` of the the line face cusp `h⁻¹ L h` (its Levi image is all of `GL₂(ℤ)`: the determinant and reflection elements are included), acting on the extension `ℤ² → E → Γ(N)` of the cusp (`N ≥ 3`), on the
radical, on the Levi `Γ(N)` and on a coefficient module `ρ̃` of `SL₃(ℤ)`.  `gammaNQAt N h` is a normal subgroup of finite index of `G` acting trivially on the cuspidal groups (`FaceAction.cuspAct_inner`), so the finite covering group is `G ⧸ gammaNQAt N h`.
`lineFace_descends_left/right`: the canonical pairing `facePairingCan` of the cuspidal groups `𝒞(H¹(N_R, ρ))`, `𝒞(H¹(N_R, ρ^*))` is perfect on the `G`-invariants.
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
theorem lineFace_inner (k : bigLineStabAt h) (hk : k ∈ (gammaNQAt N h).subgroupOf (bigLineStabAt h)) :
    ∃ e : gammaNQAt N h, (∀ e', (lineFaceAction N hN h ρ).θ k e' = e * e' * e⁻¹) ∧
      ∀ v, (lineFaceAction N hN h ρ).T k v = (lineGRep ρ N h).ρ e v := by
  refine ⟨⟨k.1, hk⟩, fun e' => Subtype.ext ?_, fun v => rfl⟩
  show (((lineGθ N hN h k) e' : gammaNQAt N h) : SL(3, ℤ)) = k.1 * e'.1 * k.1⁻¹
  exact lineGθ_val N hN h k e'

variable [FiniteDimensional ℂ (lineGRep ρ N h)]

/-- **The descended canonical pairing of the line face is perfect (left kernel).**  A class of the `G`-invariants of `𝒞(H¹(N_R, ρ))` which pairs to zero with every `G`-invariant class of `𝒞(H¹(N_R, ρ^*))` is zero. -/
theorem lineFace_descends_left
    (x : (lineFaceAction N hN h ρ).invariants (lineFaceSplitting N h))
    (hx : ∀ y : (lineFaceAction N hN h ρ).invariantsDual (lineFaceSplitting N h),
      facePairingCan hN (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) (lineGRep ρ N h) x.1 y.1 = 0) : x = 0 := by
  have := gammaNQAt_big_normal N h
  have hfi := gammaNQAt_big_finiteIndex N h hN
  have : Finite (↥(bigLineStabAt h) ⧸ (gammaNQAt N h).subgroupOf (bigLineStabAt h)) :=
    @Subgroup.finite_quotient_of_finiteIndex _ _ _ hfi
  exact (lineFaceAction N hN h ρ).cusp_descends_left (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) ((gammaNQAt N h).subgroupOf (bigLineStabAt h))
    (lineFace_inner N hN h ρ) (lineFaceAction_radDet N hN h ρ) x hx

/-- **Right kernel.** -/
theorem lineFace_descends_right
    (y : (lineFaceAction N hN h ρ).invariantsDual (lineFaceSplitting N h))
    (hy : ∀ x : (lineFaceAction N hN h ρ).invariants (lineFaceSplitting N h),
      facePairingCan hN (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) (lineGRep ρ N h) x.1 y.1 = 0) : y = 0 := by
  have := gammaNQAt_big_normal N h
  have hfi := gammaNQAt_big_finiteIndex N h hN
  have : Finite (↥(bigLineStabAt h) ⧸ (gammaNQAt N h).subgroupOf (bigLineStabAt h)) :=
    @Subgroup.finite_quotient_of_finiteIndex _ _ _ hfi
  exact (lineFaceAction N hN h ρ).cusp_descends_right (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) ((gammaNQAt N h).subgroupOf (bigLineStabAt h))
    (lineFace_inner N hN h ρ) (lineFaceAction_radDet N hN h ρ) y hy

end TernaryPeriodPolynomials.Argument.FaceDescent
