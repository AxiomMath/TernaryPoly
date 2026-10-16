module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Averaging

@[expose] public section


/-!
# `K†` comparison, the existence clause of `line_constant_term_comparison` from the literal `Γ(N)` statement

`constant_terms_of_gammaN`: every `InnerBoundary` plane class `ξ` is the plane coordinate of a global `K†`-cocycle with `InnerBoundary` line coordinate.
Proof: the literal class `c'` of `propC5_gammaN_printed` with the `Γ(N)` plane boundary of `ξ`, its `K†`-corestriction `classK c'`, the averaging step
`res_classK_plane`, the Shapiro injectivity, and `classK_edge_vanishing` for the line coordinate.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups DirectSum
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.EisensteinClass
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)

section Existence

open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

variable {N n}

include h3 hN in
/-- **`constant_terms` from the literal `Γ(N)` Proposition C.5 (existence clause, by averaging).**  Every `InnerBoundary` plane class `ξ`
is the plane coordinate of a global `K†`-cocycle whose line coordinate is `InnerBoundary`: take `ξ' ∈ 𝒞_P(E)` with the `Γ(N)` plane boundary
of `ξ`, the class `c'` of `propC5_gammaN_printed` with that plane boundary and zero flags, and its `K†`-corestriction. -/
theorem constant_terms_of_gammaN (hn : 4 ≤ n) (ξ : StratumH2 n trivialCharacter .plane)
    (hξ : InnerBoundary n trivialCharacter .plane ξ) :
    ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      (globalCoordinates n trivialCharacter c).1 = ξ ∧
      InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 := by
  obtain ⟨ξ', hξ'⟩ := phiPlane_mem_range N h3 hN n ξ hξ
  obtain ⟨TΓ, -, hex, -⟩ := propC5_gammaN_printed (N := N) (n := n) hN hn
  obtain ⟨c', hz, hp, -⟩ := hex ξ'
  have hrep : ∀ i : PlaneFaces N,
      resH2 (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_le_self (levelPrincipal N) (planeFlagAt (planeFaceRepr i))) (classPrincipal N h3 n hN c') =
      resPrincipal N (planeFlagAt (planeFaceRepr i)) (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
          (planeFlagAt (planeFaceRepr i)) ξ) := by
    intro i
    apply (planeH2Equiv N h3 (planeFaceRepr i) n trivialCharacter hN).injective
    calc planeH2Equiv N h3 (planeFaceRepr i) n trivialCharacter hN
          (resH2 (rationalCoefficientComponent n trivialCharacter)
            (fixedPointLevel_le_self (levelPrincipal N) (planeFlagAt (planeFaceRepr i))) (classPrincipal N h3 n hN c'))
        = resAtC N (planeFaceRepr i) n c' := planeH2Equiv_res_classPrincipal N (planeFaceRepr i) n h3 hN c'
      _ = rPlane N n (planeFaceRepr i) c' :=
          (congrArg (fun f => f c') (rPlane_eq_resAtC N n (planeFaceRepr i))).symm
      _ = planeBoundary N n c' i := (planeBoundary_apply N n c' i).symm
      _ = planeCuspSumEmbedding N n ξ' i := by rw [hp]
      _ = phiPlane N h3 hN n ξ i := by rw [hξ']
      _ = phiPlaneAt N h3 hN n (planeFaceRepr i) ξ := phiPlane_apply N h3 hN n ξ i
      _ = _ := rfl
  have hy := res_eq_of_reps h3 ξ (classPrincipal N h3 n hN c') hrep
  obtain ⟨c, hc⟩ : ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c = classK N h3 hN n c' :=
    Submodule.Quotient.mk_surjective _ _
  refine ⟨c, ?_, ?_⟩
  · rw [← sub_eq_zero]
    refine (eq_zero_iff_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) _).mpr fun F => ?_
    refine (map_sub (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F) _ _).trans
      (sub_eq_zero.mpr ?_)
    refine res_level_injective (rationalCoefficientComponent n trivialCharacter) (levelPrincipal N)
      (levelPrincipal_le N) (levelPrincipal_norm N) F ?_
    have e := planeCoordinate_component N n h3 hN c' c hc F
    have e' : resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
        (fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) F
          (globalCoordinates n trivialCharacter c).1) =
        resPrincipal N F (rationalCoefficientComponent n trivialCharacter)
        (resH2 (rationalCoefficientComponent n trivialCharacter) (fixedPointLevel_le_level F) (classK N h3 hN n c')) :=
      congrArg _ e
    exact e'.trans (res_classK_plane h3 hN c' ξ hy F)
  · have hpli : PlaneLocallyInner N h3 hN n c' := by
      refine (planeLocallyInner_iff_cusps N n h3 hN c').mpr fun h => ?_
      have hm := ((zeroFlags_iff_mixed N n hN c').mp hz).2 h
      have hm' : resAtC N h n c' ∈ faceCuspidalInH2 N h n := by
        have := LinearMap.congr_fun (rPlane_eq_resAtC N n h) c'
        exact this ▸ hm
      rwa [faceCuspidalInH2_eq_locallyInner] at hm'
    have he : ∀ e : Edges, resH2 (rationalCoefficientComponent n trivialCharacter)
        (fixedPointLevel_le_level e)
        (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0 := by
      intro e
      rw [hc]
      exact classK_edge_vanishing N h3 hN n c' hpli e
    exact innerBoundary_of_edgeVanishing n trivialCharacter .line c he

end Existence

end TernaryPeriodPolynomials.Argument.KDaggerComparison
