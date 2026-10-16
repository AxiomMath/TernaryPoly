module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Faces

@[expose] public section


/-!
# CMP-8 (3a): the Shapiro coordinate of a cocycle class as an explicit inhomogeneous class

`phiPlaneAt_classOf`: for a flag cocycle `z` of the level group `K†`, the coordinate `phiPlaneAt N h3 hN n h (classOf z)` is the class in Mathlib's
`H²(Γ(N) ∩ h⁻¹Ph, E_n)` (`faceRep N h n`) of the inhomogeneous cocycle `(a, b) ↦ z(1, a, ab)` evaluated at the flag `planeFlagAt h`
(`a, b` read in `GL₃(ℚ)` through `mapGL ℚ`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section
namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

omit [NeZero N] in
/-- **The Shapiro coordinate of the class of a cocycle, as an explicit inhomogeneous class.** -/
theorem phiPlaneAt_classOf (h : SL(3, ℤ))
    (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)) :
    ∃ c : groupCohomology.cocycles₂ (faceRep N h n),
      (∀ a b : gammaNPAt N h, (c : gammaNPAt N h × gammaNPAt N h → HomogeneousPoly n) (a, b) =
        z.val.val ![1, Matrix.SpecialLinearGroup.mapGL ℚ a.1,
          Matrix.SpecialLinearGroup.mapGL ℚ (a.1 * b.1)] (planeFlagAt h)) ∧
      phiPlaneAt N h3 hN n h (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z) = groupCohomology.H2π (faceRep N h n) c := by
  refine ⟨groupCohomology.mapCocycles₂ (planeEmbed N h3 h) (EdgeNat.comparison (planeEmbed N h3 h)
    (planeRep N h n trivialCharacter) (faceRep N h n) LinearMap.id (planeEmbed_hT N h n trivialCharacter h3))
    (bridgeCocycle (rationalCoefficientComponent n trivialCharacter)
      (fixedPointLevel (levelPrincipal N) (planeFlagAt h))
      (cocyclesRes (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_mono_level (levelPrincipal N) (levelPrincipal_le N) (planeFlagAt h))
        (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter) (planeFlagAt h) z))), ?_, ?_⟩
  · intro a b
    change (bridgeCocycle (rationalCoefficientComponent n trivialCharacter)
      (fixedPointLevel (levelPrincipal N) (planeFlagAt h))
      (cocyclesRes (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_mono_level (levelPrincipal N) (levelPrincipal_le N) (planeFlagAt h))
        (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter) (planeFlagAt h) z)) :
        _ × _ → HomogeneousPoly n) (planeEmbed N h3 h a, planeEmbed N h3 h b) = _
    rw [bridgeCocycle_apply]
    have e : (planeEmbed N h3 h a * planeEmbed N h3 h b) = planeEmbed N h3 h (a * b) := (map_mul _ _ _).symm
    rw [e]
    rfl
  · have e1 := fixedPointH2_classOf rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (planeFlagAt h) z
    refine (congrArg (fun t => planeH2Equiv N h3 h n trivialCharacter hN
      (resPrincipal N (planeFlagAt h) (rationalCoefficientComponent n trivialCharacter) t)) e1).trans ?_
    change EdgeNat.h2Map (planeEmbed N h3 h) (planeRep N h n trivialCharacter) (faceRep N h n) LinearMap.id
      (planeEmbed_hT N h n trivialCharacter h3) (bridge (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel (levelPrincipal N) (planeFlagAt h))
        (resH2 (rationalCoefficientComponent n trivialCharacter)
          (fixedPointLevel_mono_level (levelPrincipal N) (levelPrincipal_le N) (planeFlagAt h))
          (classOf (fixedPointLevel rationalLevel (planeFlagAt h)) (rationalCoefficientComponent n trivialCharacter)
            (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
            (planeFlagAt h) z)))) = _
    exact (congrArg (EdgeNat.h2Map (planeEmbed N h3 h) (planeRep N h n trivialCharacter) (faceRep N h n)
      LinearMap.id (planeEmbed_hT N h n trivialCharacter h3))
      (bridge_mk (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel (levelPrincipal N) (planeFlagAt h)) _)).trans
      (EdgeNat.h2Map_π _ _ _ _ _ _)

end TernaryPeriodPolynomials.Argument.KDaggerComparison
