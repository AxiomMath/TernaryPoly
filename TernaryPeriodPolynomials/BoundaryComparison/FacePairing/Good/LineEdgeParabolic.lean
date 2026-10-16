module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.EdgeSigmaPrimitive
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.EdgeStabilizerMembership
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.KLMembership
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.LowerRadicalEdgeFormula
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.LatticePairs
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CohomologyEdge

@[expose] public section


/-!
# The good-line edge class of an `InnerBoundary` line class is parabolic (M1a)

**Theorem.** For `coordinate` a `.line`-side stratum class with an `InnerBoundary` witness, the
good-line binary edge class `edgeK n hn ⟨..., fixedPointH2_mem_KL_of_innerBoundary inner⟩` lies in
the classical parabolic subspace `parabolicH1 (arithmeticBinaryRep (n+1) 0)`.

**Proof**, mirroring `Argument.CuspidalSpan.InnerPlaneEdgeParabolicProof`'s
`innerPlaneEdgeParabolic_proof` (the plane-side analogue of this exact argument):

`sigmaPrimitive_of_innerBoundary_goodLine` (`EdgeSigmaPrimitive.lean`) gives an ambient cocycle
`C : cocycles Λ₁ (ρn n)` representing the class, together with an ad hoc primitive `primitive` on
`Σ := fixedPointLevel rationalLevel (mk baseEdge)` whose `boundaryMap` matches `C`'s restriction to
`Σ`. Unfolding `boundaryMap`/`differentialOne` identifies this with the "global ambient-tuple
identity" `differentialOneRaw primitive.val = C.val.val` (hypothesis `hd` of the general-purpose
`relOn`/`relCocycleOn` tool in `ParabolicDualityIdentCore.lean`), and `primitive`'s own equivariance
gives `relOn`'s `hω` hypothesis on `Σ`.

`relOn Λ₁ (ρn n) primitive.val C hd hω goodLineRadicalInclusion
  goodLineRadicalInclusion_mem_edgeStabilizer` (Fact A, `EdgeStabilizerMembership.lean`) then gives a
cocycle `cycle` relative to the radical lattice whose class matches `C`'s (`relOn_H2`). Fact A and
Fact A′ (`goodLineLeviSection_T_mem_edgeStabilizer`) place *every* argument appearing in
`goodLineBinaryEdgeCycle_value`'s formula for `T` inside `Σ`, so each term vanishes by
`relCocycleOn_vanish`, giving `goodLineBinaryEdgeCycle n hn cycle (toGL T) = 0` — i.e. the cocycle is
already a `T`-coboundary with witness `u = 0`, which is `mem_parabolicH1_iff`'s first membership
condition. The second condition identifies `projectH1 (goodLineBinaryEdgeCycle n hn cycle)` with
`edgeK n hn ⟨..., ...⟩` via `goodLineBinaryEdgeCycle_H1`, `relativeTwoCocycleClass_apply`,
`relOn_H2` and `toH2L_classOf`, matching `edgeK`/`KL`'s own `codRestrict`/`comap`-based definitions.
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.GoodBuildingPaths.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.LineCoordinates
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **M1a.** The good-line edge class of the good-line coordinate of an `InnerBoundary` line class
is parabolic. -/
theorem goodLine_edge_parabolic_of_innerBoundary {n : ℕ} (hn : 0 < n)
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate) :
    edgeK n hn ⟨fixedPointH2 rationalLevel (ρn n) (QuotientGroup.mk rationalGoodLine : Flags .line)
        coordinate, fixedPointH2_mem_KL_of_innerBoundary inner⟩ ∈
      parabolicH1 (arithmeticBinaryRep (n + 1) 0) := by
  obtain ⟨C, hC, primitive, hprimitive⟩ := sigmaPrimitive_of_innerBoundary_goodLine inner
  have hd : ∀ a b c : RationalGL3,
      differentialOneRaw primitive.val ![a, b, c] = C.val.val ![a, b, c] :=
    fun a b c => congrFun (congrArg (fun z => z.val.val) hprimitive) ![a, b, c]
  have hω : ∀ g ∈ fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges),
      ∀ a b : RationalGL3, primitive.val ![g * a, g * b] = (ρn n) g (primitive.val ![a, b]) := by
    intro g hg a b
    have h := primitive.2
      (⟨g, hg⟩ : fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges)) ![a, b]
    have e : (fun i => g * (![a, b] : Fin 2 → RationalGL3) i) = ![g * a, g * b] := by
      funext i; fin_cases i <;> rfl
    rwa [e] at h
  set cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep n) :=
      relOn Λ₁ (ρn n) primitive.val C hd hω
        goodLineRadicalInclusion goodLineRadicalInclusion_mem_edgeStabilizer with hcycle
  rw [mem_parabolicH1_iff]
  refine ⟨goodLineBinaryEdgeCycle n hn cycle, ⟨0, ?_⟩, ?_⟩
  · have hzero : cocycleInclusion (arithmeticBinaryRep (n + 1) 0)
        (goodLineBinaryEdgeCycle n hn cycle) (SpecialLinearGroup.toGL ModularGroup.T) = 0 := by
      show goodLineBinaryEdgeCycle n hn cycle (SpecialLinearGroup.toGL ModularGroup.T) = 0
      apply Subtype.ext
      rw [goodLineBinaryEdgeCycle_value]
      have e1 : ∀ coordinate : Fin 2,
          cycle.val (goodLineLeviSection (SpecialLinearGroup.toGL ModularGroup.T),
            goodLineRadicalInclusion (lowerLeviLatticeInput
              (SpecialLinearGroup.toGL ModularGroup.T) (radicalLatticeGenerator coordinate))) = 0 :=
        fun coordinate => relCocycleOn_vanish Λ₁ (ρn n) primitive.val C hd hω
          goodLineLeviSection_T_mem_edgeStabilizer
      have e2 : ∀ coordinate : Fin 2,
          cycle.val (goodLineRadicalInclusion (radicalLatticeGenerator coordinate),
            goodLineLeviSection (SpecialLinearGroup.toGL ModularGroup.T)) = 0 :=
        fun coordinate => relCocycleOn_vanish Λ₁ (ρn n) primitive.val C hd hω
          (goodLineRadicalInclusion_mem_edgeStabilizer (radicalLatticeGenerator coordinate))
      have hzero_pair : (fun coordinate : Fin 2 => (lowerRadicalAverageEquiv n coordinate).symm
          (cycle.val (goodLineLeviSection (SpecialLinearGroup.toGL ModularGroup.T),
              goodLineRadicalInclusion (lowerLeviLatticeInput
                (SpecialLinearGroup.toGL ModularGroup.T) (radicalLatticeGenerator coordinate))) -
            cycle.val (goodLineRadicalInclusion (radicalLatticeGenerator coordinate),
              goodLineLeviSection (SpecialLinearGroup.toGL ModularGroup.T)))) =
          (0 : Fin 2 → HomogeneousPoly n) := by
        funext coordinate
        rw [e1 coordinate, e2 coordinate, sub_self]
        exact map_zero _
      rw [hzero_pair]
      exact congrArg _ (map_zero (lowerRadicalCoordinate n))
    simp only [hzero, map_zero, sub_zero]
  · show groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0)
        (goodLineBinaryEdgeCycle n hn cycle) =
      edgeK n hn ⟨fixedPointH2 rationalLevel (ρn n)
          (QuotientGroup.mk rationalGoodLine : Flags .line) coordinate,
        fixedPointH2_mem_KL_of_innerBoundary inner⟩
    rw [goodLineBinaryEdgeCycle_H1]
    show goodLineBinaryEdge n hn (relativeTwoCocycleClass goodLineRadicalInclusion
        (goodLineCoefficientRep n) cycle) =
      goodLineBinaryEdge n hn ⟨toH2L n (fixedPointH2 rationalLevel (ρn n)
          (QuotientGroup.mk rationalGoodLine : Flags .line) coordinate),
        fixedPointH2_mem_KL_of_innerBoundary inner⟩
    apply congrArg
    apply Subtype.ext
    rw [relativeTwoCocycleClass_apply]







    show groupCohomology.H2π (goodLineCoefficientRep n) cycle.val =
      toH2L n (fixedPointH2 rationalLevel (ρn n)
        (QuotientGroup.mk rationalGoodLine : Flags .line) coordinate)
    rw [← hC, toH2L_classOf]
    exact relOn_H2 Λ₁ (ρn n) primitive.val C hd hω
      goodLineRadicalInclusion goodLineRadicalInclusion_mem_edgeStabilizer

end TernaryPeriodPolynomials.Argument.FacePairing
