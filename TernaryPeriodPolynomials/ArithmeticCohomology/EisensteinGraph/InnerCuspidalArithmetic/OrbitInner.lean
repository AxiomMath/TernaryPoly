module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.StabilizerTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.SourceMatching

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

theorem fixedPointH2_eq_zero_of_orbit_representatives
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {X : Type} [MulAction RationalGL3 X]
    (level : Subgroup RationalGL3) (representation : Representation ℂ RationalGL3 V)
    (coordinate : H2 level (functionRepresentation representation X))
    (vanishing : ∀ orbit : OrbitIndex level X,
      fixedPointH2 level representation orbit.out coordinate = 0) :
    ∀ point : X, fixedPointH2 level representation point coordinate = 0 := by
  intro point
  have atRepresentative := vanishing (Quotient.mk'' point)
  change fixedPointH2 level representation (orbitRepresentative level point)
    coordinate = 0 at atRepresentative
  have transported := stabilizerTransportH2_fixedPointH2 level representation
    (orbitTransport level point) (orbitRepresentative level point) point
    (orbitTransport_spec level point) coordinate
  rw [atRepresentative, map_zero] at transported
  exact transported.symm

theorem vanishesOnGood_iff_orbit_representatives {degree : ℕ}
    {character : RankOneCharacter} {side : Side}
    (coordinate : StratumH2 degree character side) :
    VanishesOnGood degree character side coordinate ↔
      ∀ orbit : OrbitIndex rationalLevel (Flags side), GoodFlag side orbit.out →
        fixedPointH2 rationalLevel (rationalCoefficientComponent degree character)
          orbit.out coordinate = 0 := by
  rw [vanishesOnGood_iff_fixedPointH2]
  constructor
  · intro vanishing orbit good
    exact vanishing orbit.out good
  · intro vanishing flag good
    have representativeGood : GoodFlag side (orbitRepresentative rationalLevel flag) := by
      apply (goodFlag_rationalLevel_smul_iff side
        (orbitTransport rationalLevel flag) (orbitRepresentative rationalLevel flag)).mp
      rw [orbitTransport_spec]
      exact good
    have atRepresentative := vanishing (Quotient.mk'' flag) representativeGood
    change fixedPointH2 rationalLevel (rationalCoefficientComponent degree character)
      (orbitRepresentative rationalLevel flag) coordinate = 0 at atRepresentative
    have transported := stabilizerTransportH2_fixedPointH2 rationalLevel
      (rationalCoefficientComponent degree character) (orbitTransport rationalLevel flag)
      (orbitRepresentative rationalLevel flag) flag (orbitTransport_spec rationalLevel flag)
      coordinate
    rw [atRepresentative, map_zero] at transported
    exact transported.symm

theorem innerBoundary_iff_edge_orbit_representatives {degree : ℕ}
    {character : RankOneCharacter} {side : Side}
    (coordinate : StratumH2 degree character side) :
    InnerBoundary degree character side coordinate ↔
      ∀ orbit : OrbitIndex rationalLevel Edges,
        endpointStabilizerRestriction degree character side orbit.out
          (fixedPointH2 rationalLevel (rationalCoefficientComponent degree character)
            (endpoint side orbit.out) coordinate) = 0 := by
  rw [innerBoundary_iff_endpointH2]
  constructor
  · intro vanishing orbit
    rw [endpointStabilizerRestriction_fixedPointH2, vanishing, map_zero]
  · intro vanishing
    apply (eq_zero_iff_fixedPointH2 rationalLevel
      (rationalCoefficientComponent degree character) _).mpr
    apply fixedPointH2_eq_zero_of_orbit_representatives
    intro orbit
    rw [← endpointStabilizerRestriction_fixedPointH2]
    exact vanishing orbit

theorem stabilizerTransportH2_endpoint_restriction (degree : ℕ)
    (character : RankOneCharacter) (side : Side) (element : rationalLevel)
    (source target : Edges) (transports : element.val • source = target)
    (coordinate : H2 (fixedPointLevel rationalLevel (endpoint side source))
      (rationalCoefficientComponent degree character)) :
    endpointStabilizerRestriction degree character side target
        (stabilizerTransportH2 rationalLevel (rationalCoefficientComponent degree character)
          element (endpoint side source) (endpoint side target)
          (by rw [← endpoint_smul, transports]) coordinate) =
      stabilizerTransportH2 rationalLevel (rationalCoefficientComponent degree character)
        element source target transports
        (endpointStabilizerRestriction degree character side source coordinate) := by
  refine Quotient.inductionOn' coordinate ?_
  intro cycle
  rfl

theorem innerBoundary_iff_line_orbit_representatives {degree : ℕ}
    {character : RankOneCharacter} {side : Side}
    (coordinate : StratumH2 degree character side) :
    InnerBoundary degree character side coordinate ↔
      ∀ orbit : OrbitIndex rationalLevel (Flags side),
        fixedPointH2 rationalLevel (rationalCoefficientComponent degree character)
          orbit.out coordinate ∈ locallyInnerClasses degree character side orbit.out := by
  constructor
  · intro inner orbit
    exact innerBoundary_fixedPointH2_locallyInner inner orbit.out
  · intro localInner
    apply (innerBoundary_iff_endpointStabilizerRestrictions coordinate).mpr
    intro edge
    let flag := endpoint side edge
    let element := orbitTransport rationalLevel flag
    let sourceEdge := element.val⁻¹ • edge
    have sourceEndpoint : endpoint side sourceEdge = orbitRepresentative rationalLevel flag := by
      change endpoint side (element.val⁻¹ • edge) = orbitRepresentative rationalLevel flag
      rw [endpoint_smul]
      have transported := orbitTransport_spec rationalLevel flag
      exact (inv_smul_eq_iff.mpr transported.symm)
    have edgeTransport : element.val • sourceEdge = edge := smul_inv_smul _ _
    have atSource := localInner (Quotient.mk'' flag)
    change fixedPointH2 rationalLevel (rationalCoefficientComponent degree character)
      (orbitRepresentative rationalLevel flag) coordinate ∈
        locallyInnerClasses degree character side (orbitRepresentative rationalLevel flag)
      at atSource
    rw [← sourceEndpoint] at atSource
    have restriction := (Submodule.mem_iInf
      (M := H2 (fixedPointLevel rationalLevel (endpoint side sourceEdge))
        (rationalCoefficientComponent degree character)) _).mp atSource ⟨sourceEdge, rfl⟩
    change endpointStabilizerRestriction degree character side sourceEdge
      (fixedPointH2 rationalLevel (rationalCoefficientComponent degree character)
        (endpoint side sourceEdge) coordinate) = 0 at restriction
    have naturality := stabilizerTransportH2_endpoint_restriction degree character side
      element sourceEdge edge edgeTransport
      (fixedPointH2 rationalLevel (rationalCoefficientComponent degree character)
        (endpoint side sourceEdge) coordinate)
    rw [restriction, map_zero] at naturality
    have transported := stabilizerTransportH2_fixedPointH2 rationalLevel
      (rationalCoefficientComponent degree character) element (endpoint side sourceEdge)
      (endpoint side edge) (by rw [← endpoint_smul, edgeTransport]) coordinate
    exact (congrArg (endpointStabilizerRestriction degree character side edge)
      transported).symm.trans naturality

theorem mem_innerBadLineClasses_iff_orbits (degree : ℕ)
    (coordinate : StratumH2 degree trivialCharacter .line) :
    coordinate ∈ innerBadLineClasses degree ↔
      (∀ orbit : OrbitIndex rationalLevel (Flags .line), GoodFlag .line orbit.out →
        fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
          orbit.out coordinate = 0) ∧
      (∀ orbit : OrbitIndex rationalLevel (Flags .line),
        fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
          orbit.out coordinate ∈ locallyInnerClasses degree trivialCharacter .line orbit.out) := by
  rw [mem_innerBadLineClasses_iff, vanishesOnGood_iff_orbit_representatives,
    innerBoundary_iff_line_orbit_representatives]

theorem mem_automorphicLineSpan_iff_matching_bad_orbits (degree : ℕ)
    (coordinate : StratumH2 degree trivialCharacter .line)
    (good : VanishesOnGood degree trivialCharacter .line coordinate) :
    coordinate ∈ automorphicLineSpan degree ↔
      ∃ coefficients : realizedLineClasses degree →₀ ℂ,
        VanishesOnGood degree trivialCharacter .line
            (coefficients.sum (fun image scalar => scalar • image.val)) ∧
          ∀ orbit : OrbitIndex rationalLevel (Flags .line), ¬ GoodFlag .line orbit.out →
            fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
                orbit.out coordinate =
              fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
                orbit.out (coefficients.sum (fun image scalar => scalar • image.val)) := by
  constructor
  · intro membership
    obtain ⟨coefficients, sameClass⟩ :=
      (mem_automorphicLineSpan_iff_finite_sources degree coordinate).mp membership
    refine ⟨coefficients, ?_, ?_⟩
    · rw [sameClass]
      exact good
    · intro orbit _bad
      exact congrArg (fixedPointH2 rationalLevel
        (rationalCoefficientComponent degree trivialCharacter) orbit.out) sameClass.symm
  · rintro ⟨coefficients, sourceGood, badRestrictions⟩
    apply (mem_automorphicLineSpan_iff_finite_sources degree coordinate).mpr
    refine ⟨coefficients, ?_⟩
    apply orbitRestrictionH2_injective rationalLevel
      (rationalCoefficientComponent degree trivialCharacter)
    funext orbit
    change fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
        orbit.out (coefficients.sum (fun image scalar => scalar • image.val)) =
      fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
        orbit.out coordinate
    by_cases goodOrbit : GoodFlag .line orbit.out
    · exact (vanishesOnGood_fixedPointH2 sourceGood orbit.out goodOrbit).trans
        (vanishesOnGood_fixedPointH2 good orbit.out goodOrbit).symm
    · exact (badRestrictions orbit goodOrbit).symm

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
