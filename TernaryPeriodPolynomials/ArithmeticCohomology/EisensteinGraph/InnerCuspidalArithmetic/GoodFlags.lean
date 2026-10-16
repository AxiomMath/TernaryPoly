module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.OrbitReconstruction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

theorem arithmeticLevel_lastRow (element : arithmeticLevel) :
    ∀ column : Fin 3, (element.val.val 2 column : ZMod 3) = lastRow column := by
  intro column
  have row : lastRow ᵥ* (reductionThree element.val).val = lastRow := element.property
  have entry := congrFun row column
  simp only [lastRow, single_vecMul, one_smul] at entry
  exact entry

theorem arithmeticLevel_lastCoordinate (element : arithmeticLevel)
    (vector : Fin 3 → ℤ) :
    ((element.val.val *ᵥ vector) 2 : ZMod 3) = (vector 2 : ZMod 3) := by
  have mapped := (Int.castRingHom (ZMod 3)).map_mulVec element.val.val vector 2
  change ((element.val.val *ᵥ vector) 2 : ZMod 3) = _ at mapped
  rw [mapped]
  change ∑ column : Fin 3,
    (element.val.val 2 column : ZMod 3) * (vector column : ZMod 3) = _
  simp only [arithmeticLevel_lastRow element]
  simp [lastRow, Fin.sum_univ_three]

theorem integralVectorInFlag_smul (side : Side) (element : arithmeticLevel)
    (flag : Flags side) (vector : Fin 3 → ℤ)
    (integral : IntegralVectorInFlag side flag vector) :
    IntegralVectorInFlag side (rationalInclusion element • flag)
      (element.val.val *ᵥ vector) := by
  obtain ⟨representative, represented, coordinates, support, inFlag⟩ := integral
  refine ⟨rationalInclusion element * representative, ?_, coordinates, ?_, ?_⟩
  · rw [← represented]
    rfl
  · cases side <;> exact support
  · change ((GeneralLinearGroup.map (Int.castRingHom ℚ) element.val).val *
      representative.val) *ᵥ coordinates = _
    rw [← mulVec_mulVec, inFlag]
    funext index
    exact ((Int.castRingHom ℚ).map_mulVec element.val.val vector index).symm

theorem goodFlag_arithmetic_smul (side : Side) (element : arithmeticLevel)
    (flag : Flags side) (good : GoodFlag side flag) :
    GoodFlag side (rationalInclusion element • flag) := by
  obtain ⟨vector, integral, nonzero⟩ := good
  refine ⟨element.val.val *ᵥ vector,
    integralVectorInFlag_smul side element flag vector integral, ?_⟩
  rw [arithmeticLevel_lastCoordinate]
  exact nonzero

theorem goodFlag_rationalLevel_smul (side : Side) (element : rationalLevel)
    (flag : Flags side) (good : GoodFlag side flag) :
    GoodFlag side (element.val • flag) := by
  obtain ⟨integralElement, represented⟩ := element.property
  rw [← represented]
  exact goodFlag_arithmetic_smul side integralElement flag good

theorem goodFlag_rationalLevel_smul_iff (side : Side) (element : rationalLevel)
    (flag : Flags side) :
    GoodFlag side (element.val • flag) ↔ GoodFlag side flag := by
  constructor
  · intro good
    have inverse := goodFlag_rationalLevel_smul side element⁻¹ (element.val • flag) good
    simpa only [Subgroup.coe_inv, inv_smul_smul] using inverse
  · exact goodFlag_rationalLevel_smul side element flag

theorem vanishesOnGood_iff_fixedPointH2 {degree : ℕ} {character : RankOneCharacter}
    {side : Side} (coordinate : StratumH2 degree character side) :
    VanishesOnGood degree character side coordinate ↔
      ∀ flag : Flags side, GoodFlag side flag →
        fixedPointH2 rationalLevel (rationalCoefficientComponent degree character) flag
          coordinate = 0 := by
  constructor
  · intro vanishing flag good
    exact vanishesOnGood_fixedPointH2 vanishing flag good
  · refine Quotient.inductionOn' coordinate ?_
    intro cycle vanishing
    have localBoundaries : ∀ flag : Flags side,
        ∃ primitive : cochains (fixedPointLevel rationalLevel flag)
            (rationalCoefficientComponent degree character) 1,
          GoodFlag side flag →
            boundaryMap (fixedPointLevel rationalLevel flag)
                (rationalCoefficientComponent degree character) primitive =
              fixedPointCycle rationalLevel (rationalCoefficientComponent degree character)
                flag cycle := by
      intro flag
      by_cases good : GoodFlag side flag
      · have zeroClass := vanishing flag good
        change classOf (fixedPointLevel rationalLevel flag)
          (rationalCoefficientComponent degree character)
          (fixedPointCycle rationalLevel (rationalCoefficientComponent degree character)
            flag cycle) = 0 at zeroClass
        obtain ⟨primitive, boundary⟩ := (Submodule.Quotient.mk_eq_zero _).mp zeroClass
        exact ⟨primitive, fun _ => boundary⟩
      · exact ⟨0, fun impossible => False.elim (good impossible)⟩
    choose primitives boundaries using localBoundaries
    refine ⟨cycle, rfl,
      reconstructPrimitive rationalLevel (rationalCoefficientComponent degree character)
        primitives, ?_⟩
    intro vertices flag good
    have representativeGood : GoodFlag side (orbitRepresentative rationalLevel flag) := by
      apply (goodFlag_rationalLevel_smul_iff side
        (orbitTransport rationalLevel flag) (orbitRepresentative rationalLevel flag)).mp
      rw [orbitTransport_spec]
      exact good
    have boundary := congrArg
      (fun restricted => restricted.val.val
        (fun index => (orbitTransport rationalLevel flag).val⁻¹ * vertices index))
      (boundaries (orbitRepresentative rationalLevel flag) representativeGood)
    have translatedPair (first second : RationalGL3) :
        (fun index : Fin 2 => (orbitTransport rationalLevel flag).val⁻¹ *
          ![first, second] index) =
        ![(orbitTransport rationalLevel flag).val⁻¹ * first,
          (orbitTransport rationalLevel flag).val⁻¹ * second] := by
      funext index
      fin_cases index <;> rfl
    change cycle.val.val vertices flag =
      rationalCoefficientComponent degree character (orbitTransport rationalLevel flag).val
        ((primitives (orbitRepresentative rationalLevel flag)).val
          (fun index => (orbitTransport rationalLevel flag).val⁻¹ *
            ![vertices 1, vertices 2] index)) -
      rationalCoefficientComponent degree character (orbitTransport rationalLevel flag).val
        ((primitives (orbitRepresentative rationalLevel flag)).val
          (fun index => (orbitTransport rationalLevel flag).val⁻¹ *
            ![vertices 0, vertices 2] index)) +
      rationalCoefficientComponent degree character (orbitTransport rationalLevel flag).val
        ((primitives (orbitRepresentative rationalLevel flag)).val
          (fun index => (orbitTransport rationalLevel flag).val⁻¹ *
            ![vertices 0, vertices 1] index))
    simp only [translatedPair]
    rw [← map_sub, ← map_add]
    change (primitives (orbitRepresentative rationalLevel flag)).val
          ![(orbitTransport rationalLevel flag).val⁻¹ * vertices 1,
            (orbitTransport rationalLevel flag).val⁻¹ * vertices 2] -
        (primitives (orbitRepresentative rationalLevel flag)).val
          ![(orbitTransport rationalLevel flag).val⁻¹ * vertices 0,
            (orbitTransport rationalLevel flag).val⁻¹ * vertices 2] +
        (primitives (orbitRepresentative rationalLevel flag)).val
          ![(orbitTransport rationalLevel flag).val⁻¹ * vertices 0,
            (orbitTransport rationalLevel flag).val⁻¹ * vertices 1] =
      cycle.val.val (fun index => (orbitTransport rationalLevel flag).val⁻¹ * vertices index)
        (orbitRepresentative rationalLevel flag) at boundary
    rw [boundary]
    exact cochain_orbitTransport rationalLevel
      (rationalCoefficientComponent degree character) 2 cycle.val vertices flag

theorem vanishesOnGood_zero (degree : ℕ) (character : RankOneCharacter) (side : Side) :
    VanishesOnGood degree character side (0 : StratumH2 degree character side) := by
  refine ⟨0, ?_, 0, ?_⟩
  · simp
  · intro vertices flag good
    simp

theorem goodBoundaryVanishing_zero_left_iff (degree : ℕ)
    (coordinate : StratumH2 degree trivialCharacter .line) :
    GoodBoundaryVanishing degree trivialCharacter (0, coordinate) ↔
      VanishesOnGood degree trivialCharacter .line coordinate := by
  change VanishesOnGood degree trivialCharacter .plane 0 ∧
    VanishesOnGood degree trivialCharacter .line coordinate ↔ _
  constructor
  · exact And.right
  · intro vanishing
    exact ⟨vanishesOnGood_zero degree trivialCharacter .plane, vanishing⟩

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
