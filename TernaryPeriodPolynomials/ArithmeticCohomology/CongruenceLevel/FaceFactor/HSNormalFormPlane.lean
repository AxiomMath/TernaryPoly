module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSNormalForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.FrameLevel

@[expose] public section


/-!
# The normal form `U = 0` for the mixed classes of a plane cusp of `Γ(N)`

Formalized by Claude Sonnet 5.5.

`planeMixed_normal_form`: every mixed class `x ∈ planeMixedAt N h W` of the plane cusp `h⁻¹Qh` has a relative two-cocycle representative `z` (zero on the radical) with
`z(s a, s b) = 0` for the Levi splitting `s = faceSplitting N h`; `H²(Γ(N), -) = 0` is `H2_vanish_level`.  `planeMixed_crossed_edge`: the edge class of `x` is
the class of a genuine crossed homomorphism `a ↦ [splitEdgeCycle a z]`.
-/

open scoped MatrixGroups
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ)) {W : Rep ℂ ↥(gammaNPAt N h)}

/-- **Normal form of a mixed class of a plane cusp.** -/
theorem planeMixed_normal_form (x : planeMixedAt N h W) :
    ∃ z : relativeTwoCocycles (faceExt N h).inl W,
      relativeTwoCocycleClass (faceExt N h).inl W z =
        ⟨x.1, res_radical_of_planeMixedAt x⟩ ∧
      ∀ a b, z.val (faceSplitting N h a, faceSplitting N h b) = 0 :=
  exists_normal_form (faceSplitting N h) W
    (fun A z => H2_vanish_level (CongruenceSubgroup.Gamma N) A z) ⟨x.1, res_radical_of_planeMixedAt x⟩

/-- **The edge of a mixed class of a plane cusp is the class of a genuine crossed homomorphism `Γ(N) → Z¹(R, W)`.** -/
theorem planeMixed_crossed_edge (x : planeMixedAt N h W) :
    ∃ (z : relativeTwoCocycles (faceExt N h).inl W),
      relativeTwoCocycleClass (faceExt N h).inl W z = ⟨x.1, res_radical_of_planeMixedAt x⟩ ∧
      (∀ a b, splitEdgeCycle (faceSplitting N h) W (a * b) z =
        splitRadicalCocycleAction (faceSplitting N h) W a (splitEdgeCycle (faceSplitting N h) W b z) +
          splitEdgeCycle (faceSplitting N h) W a z) ∧
      splitCohomologyEdge (faceSplitting N h) W ⟨x.1, res_radical_of_planeMixedAt x⟩ =
        groupCohomology.H1π (splitRadicalH1Representation (faceSplitting N h) W)
          (splitCocycleEdge (faceSplitting N h) W z) ∧
      ∀ a, (splitCocycleEdge (faceSplitting N h) W z :
          _ → groupCohomology.H1 (Rep.res (faceExt N h).inl W)) a =
        groupCohomology.H1π (Rep.res (faceExt N h).inl W) (splitEdgeCycle (faceSplitting N h) W a z) := by
  obtain ⟨z, hz, hU⟩ := planeMixed_normal_form N h x
  obtain ⟨h1, h2, h3⟩ := splitCohomologyEdge_of_normal (faceSplitting N h) W z hU
  refine ⟨z, hz, h1, ?_, h2⟩
  rw [← hz]
  exact h3

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
