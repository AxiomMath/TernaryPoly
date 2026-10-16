module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.EdgeSigmaPrimitive
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.OddCase
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.UpperRadicalEdgeFormula
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.LeviLattice
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.Lattice

@[expose] public section


/-!
# `InnerPlaneEdgeParabolic` holds unconditionally (Input 1, Eichler–Shimura plane edge)

`OddCase.lean` isolates `InnerPlaneEdgeParabolic` as "Input 1": for a plane class `ξ` with
an `InnerBoundary` witness, `edgeH2 n hn hodd (cuspRes ...)` should lie in the classical parabolic
subspace `parabolicH1`. This file proves it unconditionally, from `InnerBoundary` alone (the
`VanishesOnGood` hypothesis is not needed).

**Proof.** `sigmaPrimitive_of_innerBoundary` (`EdgeSigmaPrimitive.lean`) gives an ambient cocycle
`C₀ : cocycles Λ₀ (ρn n)` representing the class, together with an ad hoc primitive `prim₀` on
`Σ₀ := fixedPointLevel rationalLevel standardBadEdge` whose `boundaryMap` matches `C₀`'s
restriction to `Σ₀`. Unfolding `boundaryMap`/`differentialOne` identifies this with the "global
ambient-tuple identity" `differentialOneRaw prim₀.val = C₀.val.val` (hypothesis `hd` of the
general-purpose `relOn`/`relCocycleOn` tool in `ParabolicDualityIdentCore.lean`), and `prim₀`'s own
equivariance gives `relOn`'s `hω` hypothesis on `Σ₀`.

`relOn Λ₀ (ρn n) prim₀.val C₀ hd hω identityPlaneRadicalInclusion
  identityPlaneRadicalInclusion_mem_edgeStabilizer` (Fact A, `EdgeStabilizerMembership.lean`) then
gives a cocycle relative to the radical lattice whose class matches `C₀`'s. Fact A and Fact A′
(`identityPlaneLeviSection_T_mem_edgeStabilizer`) place *every* argument appearing in
`identityPlaneBinaryEdgeCycle_value`'s four-term formula for `T` inside `Σ₀`, so each term vanishes
by `relCocycleOn_vanish`, giving `identityPlaneBinaryEdgeCycle n cycle (toGL T) = 0` — i.e. the
cocycle is already a `T`-coboundary with witness `u = 0`, which is exactly `mem_parabolicH1_iff`'s
membership condition.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates
open TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.CuspidalSpan


/-- Input 1 of `OddCase.lean`, proved unconditionally. -/
theorem innerPlaneEdgeParabolic_proof {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    InnerPlaneEdgeParabolic n hn hodd := by
  intro ξ _hvanish hinner
  obtain ⟨C₀, hC₀, prim₀, hprim₀⟩ := sigmaPrimitive_of_innerBoundary hinner
  have hd : ∀ a b c : RationalGL3,
      differentialOneRaw prim₀.val ![a, b, c] = C₀.val.val ![a, b, c] :=
    fun a b c => congrFun (congrArg (fun z => z.val.val) hprim₀) ![a, b, c]
  have hω : ∀ g ∈ fixedPointLevel rationalLevel standardBadEdge, ∀ a b : RationalGL3,
      prim₀.val ![g * a, g * b] = (ρn n) g (prim₀.val ![a, b]) := by
    intro g hg a b
    have h := prim₀.2 (⟨g, hg⟩ : fixedPointLevel rationalLevel standardBadEdge) ![a, b]
    have e : (fun i => g * (![a, b] : Fin 2 → RationalGL3) i) = ![g * a, g * b] := by
      funext i; fin_cases i <;> rfl
    rwa [e] at h
  set cycle : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep n) :=
      relOn Λ₀ (ρn n) prim₀.val C₀ hd hω
        identityPlaneRadicalInclusion identityPlaneRadicalInclusion_mem_edgeStabilizer with hcycle
  rw [mem_parabolicH1_iff]
  refine ⟨identityPlaneBinaryEdgeCycle n cycle, ⟨0, ?_⟩, ?_⟩
  · have hzero : cocycleInclusion (arithmeticBinaryRep (n + 1) (-1))
        (identityPlaneBinaryEdgeCycle n cycle) (SpecialLinearGroup.toGL ModularGroup.T) = 0 := by
      show identityPlaneBinaryEdgeCycle n cycle (SpecialLinearGroup.toGL ModularGroup.T) = 0
      apply Subtype.ext
      rw [identityPlaneBinaryEdgeCycle_value]
      have e1 : cycle.val (identityPlaneLeviSection (SpecialLinearGroup.toGL ModularGroup.T),
          identityPlaneRadicalInclusion
            (upperLeviLatticeInput (SpecialLinearGroup.toGL ModularGroup.T) radicalLatticeFirst)) = 0 :=
        relCocycleOn_vanish Λ₀ (ρn n) prim₀.val C₀ hd hω
          identityPlaneLeviSection_T_mem_edgeStabilizer
      have e2 : cycle.val (identityPlaneRadicalInclusion radicalLatticeFirst,
          identityPlaneLeviSection (SpecialLinearGroup.toGL ModularGroup.T)) = 0 :=
        relCocycleOn_vanish Λ₀ (ρn n) prim₀.val C₀ hd hω
          (identityPlaneRadicalInclusion_mem_edgeStabilizer radicalLatticeFirst)
      have e3 : cycle.val (identityPlaneLeviSection (SpecialLinearGroup.toGL ModularGroup.T),
          identityPlaneRadicalInclusion
            (upperLeviLatticeInput (SpecialLinearGroup.toGL ModularGroup.T) radicalLatticeSecond)) = 0 :=
        relCocycleOn_vanish Λ₀ (ρn n) prim₀.val C₀ hd hω
          identityPlaneLeviSection_T_mem_edgeStabilizer
      have e4 : cycle.val (identityPlaneRadicalInclusion radicalLatticeSecond,
          identityPlaneLeviSection (SpecialLinearGroup.toGL ModularGroup.T)) = 0 :=
        relCocycleOn_vanish Λ₀ (ρn n) prim₀.val C₀ hd hω
          (identityPlaneRadicalInclusion_mem_edgeStabilizer radicalLatticeSecond)
      simp only [e1, e2, e3, e4, sub_self]






      show (↑n + 1 : ℂ)⁻¹ • ((MvPolynomial.X 0 : Binary.Poly) * binaryPolynomialRestrict (0 : Poly) +
          (MvPolynomial.X 1 : Binary.Poly) * binaryPolynomialRestrict (0 : Poly)) = (0 : Binary.Poly)
      simp
    simp only [hzero, map_zero, sub_zero]
  · rw [← hC₀]
    exact ((congrArg (identityPlaneFullBinaryEdge n hn hodd)
        (relOn_H2 Λ₀ (ρn n) prim₀.val C₀ hd hω
          identityPlaneRadicalInclusion identityPlaneRadicalInclusion_mem_edgeStabilizer).symm).trans
      (identityPlaneFullBinaryEdge_relative n hn hodd cycle)).symm

end TernaryPeriodPolynomials.Argument.CuspidalSpan
