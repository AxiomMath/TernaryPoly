module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSNormalForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.FrameLevel

@[expose] public section


/-!
# The normal form `U = 0` for the mixed classes of a line cusp of `Γ(N)`

Formalized by Claude Sonnet 5.5.

`lineMixed_normal_form`: every mixed class `x ∈ lineMixedAt N h W` of the line cusp `h⁻¹Qh` has a relative two-cocycle representative `z` (zero on the radical) with
`z(s a, s b) = 0` for the Levi splitting `s = lineFaceSplitting N h`; `H²(Γ(N), -) = 0` is `H2_vanish_level`.  `lineMixed_crossed_edge`: the edge class of `x` is
the class of a genuine crossed homomorphism `a ↦ [splitEdgeCycle a z]`.
-/

open scoped MatrixGroups
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ)) {W : Rep ℂ ↥(gammaNQAt N h)}

/-- **Normal form of a mixed class of a line cusp.** -/
theorem lineMixed_normal_form (x : lineMixedAt N h W) :
    ∃ z : relativeTwoCocycles (lineFaceExt N h).inl W,
      relativeTwoCocycleClass (lineFaceExt N h).inl W z =
        ⟨x.1, res_radical_of_lineMixedAt x⟩ ∧
      ∀ a b, z.val (lineFaceSplitting N h a, lineFaceSplitting N h b) = 0 :=
  exists_normal_form (lineFaceSplitting N h) W
    (fun A z => H2_vanish_level (CongruenceSubgroup.Gamma N) A z) ⟨x.1, res_radical_of_lineMixedAt x⟩

/-- **The edge of a mixed class of a line cusp is the class of a genuine crossed homomorphism `Γ(N) → Z¹(R, W)`.** -/
theorem lineMixed_crossed_edge (x : lineMixedAt N h W) :
    ∃ (z : relativeTwoCocycles (lineFaceExt N h).inl W),
      relativeTwoCocycleClass (lineFaceExt N h).inl W z = ⟨x.1, res_radical_of_lineMixedAt x⟩ ∧
      (∀ a b, splitEdgeCycle (lineFaceSplitting N h) W (a * b) z =
        splitRadicalCocycleAction (lineFaceSplitting N h) W a (splitEdgeCycle (lineFaceSplitting N h) W b z) +
          splitEdgeCycle (lineFaceSplitting N h) W a z) ∧
      splitCohomologyEdge (lineFaceSplitting N h) W ⟨x.1, res_radical_of_lineMixedAt x⟩ =
        groupCohomology.H1π (splitRadicalH1Representation (lineFaceSplitting N h) W)
          (splitCocycleEdge (lineFaceSplitting N h) W z) ∧
      ∀ a, (splitCocycleEdge (lineFaceSplitting N h) W z :
          _ → groupCohomology.H1 (Rep.res (lineFaceExt N h).inl W)) a =
        groupCohomology.H1π (Rep.res (lineFaceExt N h).inl W) (splitEdgeCycle (lineFaceSplitting N h) W a z) := by
  obtain ⟨z, hz, hU⟩ := lineMixed_normal_form N h x
  obtain ⟨h1, h2, h3⟩ := splitCohomologyEdge_of_normal (lineFaceSplitting N h) W z hU
  refine ⟨z, hz, h1, ?_, h2⟩
  rw [← hz]
  exact h3

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
