module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.StandardBadMatching
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.OrbitInner

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {X : Type} [MulAction RationalGL3 X]

theorem stabilizerTransportCochain_comp (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (first second : level) (source middle target : X)
    (firstTransport : first.val • source = middle)
    (secondTransport : second.val • middle = target) (degree : ℕ)
    (cochain : cochains (fixedPointLevel level source) representation degree) :
    stabilizerTransportCochain level representation second middle target secondTransport degree
        (stabilizerTransportCochain level representation first source middle firstTransport
          degree cochain) =
      stabilizerTransportCochain level representation (second * first) source target
        (by rw [Subgroup.coe_mul, mul_smul, firstTransport, secondTransport]) degree cochain := by
  apply Subtype.ext
  funext vertices
  change representation second.val
      (representation first.val
        (cochain.val (fun index => first.val⁻¹ * (second.val⁻¹ * vertices index)))) =
    representation (second.val * first.val)
      (cochain.val (fun index => (second.val * first.val)⁻¹ * vertices index))
  rw [← Module.End.mul_apply, ← map_mul]
  apply congrArg (fun arguments => representation (second.val * first.val)
    (cochain.val arguments))
  funext index
  simp only [_root_.mul_inv_rev, mul_assoc]

theorem stabilizerTransportH2_comp (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (first second : level) (source middle target : X)
    (firstTransport : first.val • source = middle)
    (secondTransport : second.val • middle = target)
    (coordinate : H2 (fixedPointLevel level source) representation) :
    stabilizerTransportH2 level representation second middle target secondTransport
        (stabilizerTransportH2 level representation first source middle firstTransport
          coordinate) =
      stabilizerTransportH2 level representation (second * first) source target
        (by rw [Subgroup.coe_mul, mul_smul, firstTransport, secondTransport]) coordinate := by
  refine Quotient.inductionOn' coordinate ?_
  intro cycle
  apply congrArg (classOf (fixedPointLevel level target) representation)
  apply Subtype.ext
  exact stabilizerTransportCochain_comp level representation first second source middle
    target firstTransport secondTransport 2 cycle.val

theorem stabilizerTransportH2_self (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (element : level) (point : X) (fixes : element.val • point = point)
    (coordinate : H2 (fixedPointLevel level point) representation) :
    stabilizerTransportH2 level representation element point point fixes coordinate =
      coordinate := by
  refine Quotient.inductionOn' coordinate ?_
  intro cycle
  apply congrArg (classOf (fixedPointLevel level point) representation)
  apply Subtype.ext
  apply Subtype.ext
  funext vertices
  have equivariance := cycle.val.property
    ⟨element.val, element.property, MulAction.mem_stabilizer_iff.mpr fixes⟩
    (fun index => element.val⁻¹ * vertices index)
  change representation element.val
    (cycle.val.val (fun index => element.val⁻¹ * vertices index)) = cycle.val.val vertices
  simpa only [mul_inv_cancel_left] using equivariance.symm

theorem stabilizerTransportH2_inverse (level : Subgroup RationalGL3)
    (representation : Representation ℂ RationalGL3 V)
    (element : level) (source target : X) (transports : element.val • source = target)
    (coordinate : H2 (fixedPointLevel level source) representation) :
    stabilizerTransportH2 level representation element⁻¹ target source
        (by rw [Subgroup.coe_inv, ← transports, inv_smul_smul])
        (stabilizerTransportH2 level representation element source target transports
          coordinate) = coordinate := by
  rw [stabilizerTransportH2_comp]
  exact stabilizerTransportH2_self level representation (element⁻¹ * element) source
    (by simp) coordinate

theorem stabilizerTransportH2_locallyInner (degree : ℕ) (character : RankOneCharacter)
    (side : Side) (element : rationalLevel) (source target : Flags side)
    (transports : element.val • source = target)
    (coordinate : H2 (fixedPointLevel rationalLevel source)
      (rationalCoefficientComponent degree character))
    (inner : coordinate ∈ locallyInnerClasses degree character side source) :
    stabilizerTransportH2 rationalLevel (rationalCoefficientComponent degree character)
        element source target transports coordinate ∈
      locallyInnerClasses degree character side target := by
  apply (Submodule.mem_iInf
    (M := H2 (fixedPointLevel rationalLevel target)
      (rationalCoefficientComponent degree character)) _).mpr
  rintro ⟨edge, edgeEndpoint⟩
  let previousEdge := element.val⁻¹ • edge
  have previousEndpoint : endpoint side previousEdge = source := by
    change endpoint side (element.val⁻¹ • edge) = source
    rw [endpoint_smul, edgeEndpoint, ← transports, inv_smul_smul]
  have edgeTransport : element.val • previousEdge = edge := smul_inv_smul _ _
  have restriction := (Submodule.mem_iInf
    (M := H2 (fixedPointLevel rationalLevel source)
      (rationalCoefficientComponent degree character)) _).mp inner
      ⟨previousEdge, previousEndpoint⟩
  cases edgeEndpoint
  cases previousEndpoint
  change endpointStabilizerRestriction degree character side previousEdge coordinate = 0
    at restriction
  have naturality := stabilizerTransportH2_endpoint_restriction degree character side
    element previousEdge edge edgeTransport coordinate
  rw [restriction, map_zero] at naturality
  exact naturality

theorem innerBoundary_of_good_vanishing_standardBadLine {degree : ℕ}
    {coordinate : StratumH2 degree trivialCharacter .line}
    (good : VanishesOnGood degree trivialCharacter .line coordinate)
    (inner : fixedPointH2 rationalLevel
      (rationalCoefficientComponent degree trivialCharacter) standardBadLine coordinate ∈
        locallyInnerClasses degree trivialCharacter .line standardBadLine) :
    InnerBoundary degree trivialCharacter .line coordinate := by
  apply (innerBoundary_iff_locallyInner coordinate).mpr
  intro flag
  by_cases goodFlag : GoodFlag .line flag
  · rw [vanishesOnGood_fixedPointH2 good flag goodFlag]
    exact Submodule.zero_mem _
  · obtain ⟨element, transported⟩ := badLine_is_standardBadLine_orbit flag goodFlag
    rw [← stabilizerTransportH2_fixedPointH2 rationalLevel
      (rationalCoefficientComponent degree trivialCharacter) element standardBadLine flag
      transported coordinate]
    exact stabilizerTransportH2_locallyInner degree trivialCharacter .line element
      standardBadLine flag transported _ inner

theorem exists_innerBadLine_of_local (degree : ℕ)
    (localClass : locallyInnerClasses degree trivialCharacter .line standardBadLine) :
    ∃ coordinate : innerBadLineClasses degree,
      fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
        standardBadLine coordinate.val = localClass.val := by
  classical
  let localClasses : ∀ orbit : OrbitIndex rationalLevel (Flags .line),
      H2 (fixedPointLevel rationalLevel orbit.out)
        (rationalCoefficientComponent degree trivialCharacter) := fun orbit =>
    if good : GoodFlag .line orbit.out then 0 else
      stabilizerTransportH2 rationalLevel
        (rationalCoefficientComponent degree trivialCharacter)
        (Classical.choose (badLine_is_standardBadLine_orbit orbit.out good))
        standardBadLine orbit.out
        (Classical.choose_spec (badLine_is_standardBadLine_orbit orbit.out good))
        localClass.val
  obtain ⟨coordinate, restrictions⟩ := orbitRestrictionH2_surjective rationalLevel
    (rationalCoefficientComponent degree trivialCharacter) localClasses
  have good : VanishesOnGood degree trivialCharacter .line coordinate := by
    apply (vanishesOnGood_iff_orbit_representatives coordinate).mpr
    intro orbit goodFlag
    have restriction := congrFun restrictions orbit
    change fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
      orbit.out coordinate = localClasses orbit at restriction
    simpa only [localClasses, dite_eq_left goodFlag] using restriction
  let standardOrbit : OrbitIndex rationalLevel (Flags .line) :=
    Quotient.mk'' standardBadLine
  let standardRepresentative := orbitRepresentative rationalLevel standardBadLine
  have representativeBad : ¬ GoodFlag .line standardRepresentative := by
    intro representativeGood
    apply standardBadLine_not_good
    have standardGood := goodFlag_rationalLevel_smul .line
      (orbitTransport rationalLevel standardBadLine) standardRepresentative representativeGood
    rw [orbitTransport_spec] at standardGood
    exact standardGood
  let first := Classical.choose
    (badLine_is_standardBadLine_orbit standardRepresentative representativeBad)
  have firstTransport : first.val • standardBadLine = standardRepresentative :=
    Classical.choose_spec
      (badLine_is_standardBadLine_orbit standardRepresentative representativeBad)
  let second := orbitTransport rationalLevel standardBadLine
  have secondTransport : second.val • standardRepresentative = standardBadLine :=
    orbitTransport_spec rationalLevel standardBadLine
  have restriction := congrFun restrictions standardOrbit
  change fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
    standardRepresentative coordinate = localClasses standardOrbit at restriction
  have representativeValue : localClasses standardOrbit =
      stabilizerTransportH2 rationalLevel
        (rationalCoefficientComponent degree trivialCharacter) first standardBadLine
        standardRepresentative firstTransport localClass.val := by
    exact dite_eq_right representativeBad
  have standardValue : fixedPointH2 rationalLevel
      (rationalCoefficientComponent degree trivialCharacter) standardBadLine coordinate =
        localClass.val := by
    rw [← stabilizerTransportH2_fixedPointH2 rationalLevel
      (rationalCoefficientComponent degree trivialCharacter) second standardRepresentative
      standardBadLine secondTransport coordinate, restriction, representativeValue,
      stabilizerTransportH2_comp]
    exact stabilizerTransportH2_self rationalLevel
      (rationalCoefficientComponent degree trivialCharacter) (second * first) standardBadLine
      (by rw [Subgroup.coe_mul, mul_smul, firstTransport, secondTransport]) localClass.val
  have inner : InnerBoundary degree trivialCharacter .line coordinate :=
    innerBoundary_of_good_vanishing_standardBadLine good
      (standardValue.symm ▸ localClass.property)
  exact ⟨⟨coordinate, (mem_innerBadLineClasses_iff degree coordinate).mpr ⟨good, inner⟩⟩,
    standardValue⟩

def innerBadLineLocalRestriction (degree : ℕ) :
    innerBadLineClasses degree →ₗ[ℂ]
      locallyInnerClasses degree trivialCharacter .line standardBadLine :=
  ((fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
    standardBadLine).comp (innerBadLineClasses degree).subtype).codRestrict _ (by
      intro coordinate
      exact innerBoundary_fixedPointH2_locallyInner
        ((mem_innerBadLineClasses_iff degree coordinate.val).mp coordinate.property).2
        standardBadLine)

theorem innerBadLineLocalRestriction_bijective (degree : ℕ) :
    Function.Bijective (innerBadLineLocalRestriction degree) := by
  constructor
  · intro first second sameRestriction
    apply innerBadLine_standardRestriction_injective degree
    exact congrArg Subtype.val sameRestriction
  · intro localClass
    obtain ⟨coordinate, restricted⟩ := exists_innerBadLine_of_local degree localClass
    exact ⟨coordinate, Subtype.ext restricted⟩

def innerBadLineLocalEquiv (degree : ℕ) :
    innerBadLineClasses degree ≃ₗ[ℂ]
      locallyInnerClasses degree trivialCharacter .line standardBadLine :=
  LinearEquiv.ofBijective (innerBadLineLocalRestriction degree)
    (innerBadLineLocalRestriction_bijective degree)

def goodVanishingLineClasses (degree : ℕ) :
    Submodule ℂ (StratumH2 degree trivialCharacter .line) :=
  ⨅ flag : {flag : Flags .line // GoodFlag .line flag},
    LinearMap.ker (fixedPointH2 rationalLevel
      (rationalCoefficientComponent degree trivialCharacter) flag.val)

theorem mem_goodVanishingLineClasses_iff (degree : ℕ)
    (coordinate : StratumH2 degree trivialCharacter .line) :
    coordinate ∈ goodVanishingLineClasses degree ↔
      VanishesOnGood degree trivialCharacter .line coordinate := by
  rw [vanishesOnGood_iff_fixedPointH2]
  constructor
  · intro membership flag good
    exact (Submodule.mem_iInf
      (M := StratumH2 degree trivialCharacter .line) _).mp membership ⟨flag, good⟩
  · intro vanishing
    apply (Submodule.mem_iInf
      (M := StratumH2 degree trivialCharacter .line) _).mpr
    intro flag
    exact vanishing flag.val flag.property

def automorphicGoodLocalImage (degree : ℕ) :
    Submodule ℂ (H2 (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter)) :=
  (automorphicLineSpan degree ⊓ goodVanishingLineClasses degree).map
    (fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
      standardBadLine)

theorem mem_automorphicGoodLocalImage_iff (degree : ℕ)
    (localClass : H2 (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter)) :
    localClass ∈ automorphicGoodLocalImage degree ↔
      ∃ coefficients : realizedLineClasses degree →₀ ℂ,
        VanishesOnGood degree trivialCharacter .line
          (coefficients.sum (fun image scalar => scalar • image.val)) ∧
        fixedPointH2 rationalLevel (rationalCoefficientComponent degree trivialCharacter)
          standardBadLine (coefficients.sum (fun image scalar => scalar • image.val)) =
            localClass := by
  constructor
  · rintro ⟨coordinate, membership, restriction⟩
    obtain ⟨coefficients, sameClass⟩ :=
      (mem_automorphicLineSpan_iff_finite_sources degree coordinate).mp membership.1
    refine ⟨coefficients, ?_, ?_⟩
    · rw [sameClass]
      exact (mem_goodVanishingLineClasses_iff degree coordinate).mp membership.2
    · exact (congrArg (fixedPointH2 rationalLevel
        (rationalCoefficientComponent degree trivialCharacter) standardBadLine)
        sameClass).trans restriction
  · rintro ⟨coefficients, good, restriction⟩
    exact ⟨coefficients.sum (fun image scalar => scalar • image.val),
      ⟨(mem_automorphicLineSpan_iff_finite_sources degree _).mpr ⟨coefficients, rfl⟩,
        (mem_goodVanishingLineClasses_iff degree _).mpr good⟩, restriction⟩

theorem innerBadLine_le_automorphic_iff_local (degree : ℕ) :
    innerBadLineClasses degree ≤ automorphicLineSpan degree ↔
      locallyInnerClasses degree trivialCharacter .line standardBadLine ≤
        automorphicGoodLocalImage degree := by
  constructor
  · intro spanning localClass inner
    obtain ⟨coordinate, restriction⟩ := exists_innerBadLine_of_local degree ⟨localClass, inner⟩
    exact ⟨coordinate.val,
      ⟨spanning coordinate.property,
        (mem_goodVanishingLineClasses_iff degree coordinate.val).mpr
          ((mem_innerBadLineClasses_iff degree coordinate.val).mp coordinate.property).1⟩,
      restriction⟩
  · intro spanning coordinate inner
    obtain ⟨good, innerBoundary⟩ := (mem_innerBadLineClasses_iff degree coordinate).mp inner
    have localInner := innerBoundary_fixedPointH2_locallyInner innerBoundary standardBadLine
    obtain ⟨image, membership, sameRestriction⟩ := spanning localInner
    have imageGood := (mem_goodVanishingLineClasses_iff degree image).mp membership.2
    have sameClass := eq_of_good_vanishing_standardBadLine good imageGood sameRestriction.symm
    exact sameClass.symm ▸ membership.1

theorem inner_bad_line_cuspidal_span_iff_local :
    (∀ n : ℕ, 0 < n → ∀ a : StratumH2 n trivialCharacter .line,
      VanishesOnGood n trivialCharacter .line a → InnerBoundary n trivialCharacter .line a →
        a ∈ automorphicLineSpan n) ↔
      ∀ degree : ℕ, 0 < degree →
        locallyInnerClasses degree trivialCharacter .line standardBadLine ≤
          automorphicGoodLocalImage degree := by
  constructor
  · intro spanning degree positive
    apply (innerBadLine_le_automorphic_iff_local degree).mp
    intro coordinate membership
    obtain ⟨good, inner⟩ := (mem_innerBadLineClasses_iff degree coordinate).mp membership
    exact spanning degree positive coordinate good inner
  · intro localSpanning degree positive coordinate good inner
    exact (innerBadLine_le_automorphic_iff_local degree).mpr
      (localSpanning degree positive)
      ((mem_innerBadLineClasses_iff degree coordinate).mpr ⟨good, inner⟩)

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
