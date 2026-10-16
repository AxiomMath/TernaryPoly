module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.GoodBoundarySubmodule

@[expose] public section


/-! A conditional decomposition of the five paper statements.
This module imports definitions and proved lemmas only. Each field below is the
exact statement of an independently evaluable child statement. -/

noncomputable section
namespace GeneralEisenstein
open Homogeneous Adelic

/-- Separate mathematical proof inputs for the bridge step. -/
structure PolynomialBridgePieces where
  paths : ∃ τ : rationalLevel → EdgeChains, IsPathFamily τ
  functional : ∀ n : ℕ, 0 < n → ∀ f : HomogeneousPoly n, SymmetricSolution f →
      ∃ F : EdgeChains →ₗ[ℂ] HomogeneousPoly n, IsPolynomialFunctional f F
  realization : ∀ n : ℕ, 0 < n → ∀ f : HomogeneousPoly n, SymmetricSolution f →
      ∀ F : EdgeChains →ₗ[ℂ] HomogeneousPoly n, IsPolynomialFunctional f F →
      ∀ τ : rationalLevel → EdgeChains, IsPathFamily τ →
        ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
          RealizesPathClass F τ c
  independence : ∀ n : ℕ, 0 < n → ∀ f : HomogeneousPoly n, SymmetricSolution f →
      ∀ F : EdgeChains →ₗ[ℂ] HomogeneousPoly n, IsPolynomialFunctional f F →
      ∀ (τ : rationalLevel → EdgeChains)
        (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)),
      IsPathFamily τ → RealizesPathClass F τ c →
      ∀ τ' c', IsPathFamily τ' → RealizesPathClass F τ' c' →
        classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c' = classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c
  good : ∀ n : ℕ, 0 < n → ∀ f : HomogeneousPoly n, SymmetricSolution f →
      ∀ F : EdgeChains →ₗ[ℂ] HomogeneousPoly n, IsPolynomialFunctional f F →
      ∀ (τ : rationalLevel → EdgeChains)
        (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)),
      IsPathFamily τ → RealizesPathClass F τ c →
      GoodBoundaryVanishing n trivialCharacter (globalCoordinates n trivialCharacter c)
  normalization : ∀ n : ℕ, 0 < n → ∀ f : HomogeneousPoly n, SymmetricSolution f →
      ∀ F : EdgeChains →ₗ[ℂ] HomogeneousPoly n, IsPolynomialFunctional f F →
      ∀ (τ₀ : rationalLevel → EdgeChains)
        (c₀ : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)),
      IsPathFamily τ₀ → RealizesPathClass F τ₀ c₀ →
      ∃ (τ : rationalLevel → EdgeChains)
        (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)),
        IsPathFamily τ ∧ RealizesPathClass F τ c ∧ NormalizedBadLine f c ∧
        classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c = classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c₀
  inner : ∀ n : ℕ, 0 < n → ∀ f : HomogeneousPoly n, SymmetricSolution f →
      ∀ F : EdgeChains →ₗ[ℂ] HomogeneousPoly n, IsPolynomialFunctional f F →
      ∀ (τ : rationalLevel → EdgeChains)
        (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)),
      IsPathFamily τ → RealizesPathClass F τ c →
      NormalizedBadLine f c →
        InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2
  detection : ∀ n : ℕ, 0 < n → ∀ f : HomogeneousPoly n, SymmetricSolution f →
      ∀ F : EdgeChains →ₗ[ℂ] HomogeneousPoly n, IsPolynomialFunctional f F →
      ∀ (τ : rationalLevel → EdgeChains)
        (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)),
      IsPathFamily τ → RealizesPathClass F τ c →
      NormalizedBadLine f c →
        (globalCoordinates n trivialCharacter c).2 = 0 → bernoulliObstruction f = 0

/-- Separate mathematical proof inputs for the recognition step. -/
structure CuspidalRecognitionPieces where
  hecke : ∀ (n : ℕ) (χ : RankOneCharacter),
      ∃ hecke : BoundaryHecke n χ, ActualBoundaryHecke n χ hecke
  span : ∀ n : ℕ, 0 < n → ∀ a : StratumH2 n trivialCharacter .line,
      VanishesOnGood n trivialCharacter .line a → InnerBoundary n trivialCharacter .line a →
      a ∈ automorphicLineSpan n
  projectors : ∀ n : ℕ, 0 < n → ∀ D : CohomologicalCuspData n,
      ∀ hecke : BoundaryHecke n trivialCharacter, ActualBoundaryHecke n trivialCharacter hecke →
      ∃ p : Module.End ℂ (BoundaryCoordinates n trivialCharacter),
        IsIsotypicalProjection D.inducingData hecke p ∧
        ∀ p', IsIsotypicalProjection D.inducingData hecke p' → p' = p
  recovery : ∀ n : ℕ, 0 < n →
      ∀ hecke : BoundaryHecke n trivialCharacter, ActualBoundaryHecke n trivialCharacter hecke →
      ∀ p : CohomologicalCuspData n → Module.End ℂ (BoundaryCoordinates n trivialCharacter),
      (∀ D : CohomologicalCuspData n, IsIsotypicalProjection D.inducingData hecke (p D)) →
      ∀ b : BoundaryCoordinates n trivialCharacter, b.2 ∈ automorphicLineSpan n →
      ∃ (m : ℕ) (D : Fin m → CohomologicalCuspData n), ∑ i, (p (D i) b).2 = b.2

/-- Separate mathematical proof inputs for the holomorphy step. -/
structure EisensteinHolomorphyPieces where
  flat : ∀ (n : ℕ) (D : InducingData n),
      ∀ f : AdelicGL → ℂ, IsInduced D .plane cohomologicalPoint f →
      ∃ F : ℂ → AdelicGL → ℂ, IsFlatSection D F ∧ F cohomologicalPoint = f
  continuation : ∀ (n : ℕ) (D : InducingData n), ∀ F : ℂ → AdelicGL → ℂ,
      IsFlatSection D F → ∃ E : ℂ → AdelicGL → ℂ, IsEisensteinContinuation F E
  regularization : ∀ n : ℕ, 0 < n → ∀ D : InducingData n, D.chi = trivialCharacter →
      ∀ F : ℂ → AdelicGL → ℂ, IsFlatSection D F →
      ∀ E : ℂ → AdelicGL → ℂ, IsEisensteinContinuation F E →
      ∃ E' : ℂ → AdelicGL → ℂ,
        IsEisensteinContinuation F E' ∧ SameOffCohomologicalPoint E E' ∧
        ∀ g, AnalyticAt ℂ (fun z => E' z g) cohomologicalPoint

/-- Separate mathematical proof inputs for the projection step. -/
structure GoodProjectionPieces where
  stability : ∀ n : ℕ, 0 < n → ∀ D : InducingData n,
      ∀ hecke : BoundaryHecke n D.chi, ActualBoundaryHecke n D.chi hecke →
      ∀ t : HeckeCorrespondence, AwayThree t → ∀ b : BoundaryCoordinates n D.chi,
      GoodBoundaryVanishing n D.chi b → GoodBoundaryVanishing n D.chi (pairHecke D hecke t b)
  algebra : ∀ n : ℕ, 0 < n → ∀ D : InducingData n,
      ∀ hecke : BoundaryHecke n D.chi, ActualBoundaryHecke n D.chi hecke →
      ∀ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D hecke p →
      p ∈ awayThreeHeckeAlgebra D hecke

/-- Separate mathematical proof inputs for the detection step. -/
structure BadPlaneDetectionPieces where
  representative : ∀ n : ℕ, 0 < n → ∀ D : InducingData n, D.chi = trivialCharacter →
      ∀ ξ : boundarySummand D .plane, VanishesOnGood n D.chi .plane ξ.val →
      BadPlaneRepresentative D ξ
  sphericity : ∀ n : ℕ, 0 < n → ∀ D : InducingData n, D.chi = trivialCharacter →
      ∀ ξ : boundarySummand D .plane, ξ ≠ 0 → BadPlaneRepresentative D ξ →
      SphericalCusp D.cusp
  parity : ∀ n : ℕ, 0 < n → ∀ D : InducingData n, D.chi = trivialCharacter →
      SphericalCusp D.cusp → Odd n
  localEntry : LocalBadPlaneEntry
  globalDetection : LocalBadPlaneEntry → ∀ n : ℕ, 0 < n → Odd n →
      ∀ D : InducingData n, D.chi = trivialCharacter → SphericalCusp D.cusp →
      PlaneEisensteinHolomorphic D →
      ∀ T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line,
      RealizesStandard D T → ∀ ξ : boundarySummand D .plane,
      BadPlaneRepresentative D ξ → VanishesOnGood n D.chi .line (T ξ).val → ξ = 0

/-- The eight polynomial results recover the exact, unchanged parent bridge. -/
theorem polynomial_boundary_bridge_of_pieces (H : PolynomialBridgePieces)
    (n : ℕ) (hn : 0 < n) (f : HomogeneousPoly n) (hf : SymmetricSolution f) :
    PolynomialBoundaryBridge f := by
  rcases H.functional n hn f hf with ⟨F, hF⟩
  rcases H.paths with ⟨τ₀, hτ₀⟩
  rcases H.realization n hn f hf F hF τ₀ hτ₀ with ⟨c₀, hc₀⟩
  rcases H.normalization n hn f hf F hF τ₀ c₀ hτ₀ hc₀ with
    ⟨τ, c, hτ, hc, hnorm, _⟩
  refine ⟨F, τ, c, hF, hτ, hc, ?_, H.good n hn f hf F hF τ c hτ hc,
    H.inner n hn f hf F hF τ c hτ hc hnorm, hnorm.1, hnorm.2.1,
    hnorm.2.2.1, hnorm.2.2.2, H.detection n hn f hf F hF τ c hτ hc hnorm⟩
  exact H.independence n hn f hf F hF τ c hτ hc

/-- Actual Hecke descent, cuspidal spanning, projector construction and finite
recovery compose into the exact parent recognition statement. -/
theorem boundary_cuspidal_recognition_of_pieces (H : CuspidalRecognitionPieces)
    (n : ℕ) (hn : 0 < n) (b : BoundaryCoordinates n trivialCharacter)
    (hgood : GoodBoundaryVanishing n trivialCharacter b)
    (hinner : InnerBoundary n trivialCharacter .line b.2) : CuspidalRecognition n b := by
  classical
  rcases H.hecke n trivialCharacter with ⟨hecke, hhecke⟩
  have hex := fun D : CohomologicalCuspData n => H.projectors n hn D hecke hhecke
  choose p hp _ using hex
  rcases H.recovery n hn hecke hhecke p hp b (H.span n hn b.2 hgood.2 hinner) with
    ⟨m, D, hsum⟩
  exact ⟨hecke, hhecke, m, D, fun i => p (D i), fun i => hp (D i), hsum⟩

/-- Flat extension, actual meromorphic continuation, and single-point
regularization prove precisely the graph problem's holomorphy hypothesis. -/
theorem eisenstein_holomorphy_of_pieces (H : EisensteinHolomorphyPieces)
    (n : ℕ) (hn : 0 < n) (D : InducingData n) (hχ : D.chi = trivialCharacter) :
    PlaneEisensteinHolomorphic D := by
  refine ⟨H.flat n D, ?_⟩
  intro F hF
  rcases H.continuation n D F hF with ⟨E, hE⟩
  rcases H.regularization n hn D hχ F hF E hE with ⟨E', hE', _, hanalytic⟩
  exact ⟨E', hE', hanalytic⟩

/-- Invariance under genuine away-three generators extends to their algebra,
which contains the associate-pair projector. No extra closure statement is needed. -/
theorem boundary_projection_good_cusps_of_pieces (H : GoodProjectionPieces)
    (n : ℕ) (hn : 0 < n) (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (p : Module.End ℂ (BoundaryCoordinates n D.chi))
    (hp : IsIsotypicalProjection D hecke p) (b : BoundaryCoordinates n D.chi)
    (hb : GoodBoundaryVanishing n D.chi b) : GoodBoundaryVanishing n D.chi (p b) := by
  apply (mem_goodBoundarySubmodule n D.chi (p b)).mp
  refine adjoin_preserves_submodule (goodBoundarySubmodule n D.chi)
    {A | ∃ t, AwayThree t ∧ A = pairHecke D hecke t} ?_ p
    (H.algebra n hn D hecke hhecke p hp) b hb
  rintro A ⟨t, ht, rfl⟩ v hv
  exact H.stability n hn D hecke hhecke t ht v hv

/-- Same-constituent support, level-one sphericity, parity, the literal local
entry and global detection recover the exact parent standard-map statement. -/
theorem eisenstein_bad_plane_detection_of_pieces (H : BadPlaneDetectionPieces)
    (n : ℕ) (hn : 0 < n) (D : InducingData n) (hχ : D.chi = trivialCharacter)
    (hhol : PlaneEisensteinHolomorphic D)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line)
    (hT : RealizesStandard D T) (ξ : boundarySummand D .plane)
    (hplane : VanishesOnGood n D.chi .plane ξ.val)
    (hline : VanishesOnGood n D.chi .line (T ξ).val) : ξ = 0 := by
  classical
  by_cases hzero : ξ = 0
  · exact hzero
  have hrep := H.representative n hn D hχ ξ hplane
  have hspherical := H.sphericity n hn D hχ ξ hzero hrep
  exact H.globalDetection H.localEntry n hn (H.parity n hn D hχ hspherical)
    D hχ hspherical hhol T hT ξ hrep hline

/-- The 22 child statements and the unchanged graph proposition give the paper assembly without any glue premise. -/
theorem eisensteinInputsOfPieces
    (B : PolynomialBridgePieces) (C : CuspidalRecognitionPieces)
    (E : EisensteinHolomorphyPieces) (P : GoodProjectionPieces)
    (N : BadPlaneDetectionPieces)
    (graph : ∀ n, ∀ D : InducingData n, PlaneEisensteinHolomorphic D → GraphConclusion D) :
    EisensteinInputs where
  bridge := polynomial_boundary_bridge_of_pieces B
  recognition := boundary_cuspidal_recognition_of_pieces C
  holomorphy := eisenstein_holomorphy_of_pieces E
  graph := graph
  projection := boundary_projection_good_cusps_of_pieces P
  detection := eisenstein_bad_plane_detection_of_pieces N

/-- Conditional closure of the paper's Eisenstein obstruction step. -/
theorem bernoulli_obstruction_vanishes_of_pieces
    (B : PolynomialBridgePieces) (C : CuspidalRecognitionPieces)
    (E : EisensteinHolomorphyPieces) (P : GoodProjectionPieces)
    (N : BadPlaneDetectionPieces)
    (graph : ∀ n, ∀ D : InducingData n, PlaneEisensteinHolomorphic D → GraphConclusion D)
    (n : ℕ) (hn : 0 < n) (f : HomogeneousPoly n) (hf : SymmetricSolution f) :
    bernoulliObstruction f = 0 :=
  bernoulli_obstruction_vanishes_of_challenges
    (eisensteinInputsOfPieces B C E P N graph) n hn f hf

end GeneralEisenstein
end
