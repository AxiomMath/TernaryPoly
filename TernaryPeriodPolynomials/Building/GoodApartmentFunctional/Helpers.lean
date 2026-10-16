module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic
open Matrix

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers

noncomputable section

def goodEdges : Set Edges :=
  {edge | GoodFlag .plane (endpoint .plane edge) ∧
    GoodFlag .line (endpoint .line edge)}

def goodChains : Submodule ℂ EdgeChains :=
  Finsupp.supported ℂ ℂ goodEdges

def goodCycles : Submodule ℂ EdgeChains :=
  LinearMap.ker chainBoundary ⊓ goodChains

theorem mem_goodChains (chain : EdgeChains) :
    chain ∈ goodChains ↔ GoodChain chain := by
  rw [goodChains, Finsupp.mem_supported]
  rfl

theorem mem_goodCycles (chain : EdgeChains) :
    chain ∈ goodCycles ↔ GoodCycle chain := by
  change (chainBoundary chain = 0 ∧ chain ∈ goodChains) ↔ _
  rw [mem_goodChains]
  rfl

theorem extend_goodCycles {n : ℕ}
    (functional : goodCycles →ₗ[ℂ] HomogeneousPoly n) :
    ∃ extension : EdgeChains →ₗ[ℂ] HomogeneousPoly n,
      ∀ chain : goodCycles, extension chain.val = functional chain := by
  obtain ⟨extension, agreement⟩ := LinearMap.exists_extend functional
  refine ⟨extension, ?_⟩
  intro chain
  exact LinearMap.congr_fun agreement chain

theorem translateChain_single (groupElement : RationalGL3) (edge : Edges)
    (coefficient : ℂ) :
    translateChain groupElement (Finsupp.single edge coefficient) =
      Finsupp.single (groupElement • edge) coefficient := by
  simp [translateChain]

theorem translateChain_apartment (groupElement frame : RationalGL3) :
    translateChain groupElement (apartment frame) = apartment (groupElement * frame) := by
  simp only [apartment, map_add, map_sub, translateChain_single]
  have action_mk (representative : RationalGL3) :
      (groupElement • QuotientGroup.mk representative : Edges) =
        QuotientGroup.mk (groupElement * representative) := rfl
  simp only [action_mk, mul_assoc]

theorem chainBoundary_single (edge : Edges) (coefficient : ℂ) :
    chainBoundary (Finsupp.single edge coefficient) =
      coefficient • (Finsupp.single (Sum.inl (endpoint .plane edge)) 1 -
        Finsupp.single (Sum.inr (endpoint .line edge)) 1) := by
  simp [chainBoundary]

theorem endpoint_mk (side : Side) (frame : RationalGL3) :
    endpoint side (QuotientGroup.mk frame) = QuotientGroup.mk frame := rfl

theorem plane_swapFirstTwo (frame : RationalGL3) :
    (QuotientGroup.mk (frame * swapFirstTwo) : Flags .plane) =
      QuotientGroup.mk frame := by
  apply QuotientGroup.eq.mpr
  simp only [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  change InPlaneParabolic swapFirstTwo⁻¹
  exact ⟨rfl, rfl⟩

theorem line_swapFirstTwo (frame : RationalGL3) :
    (QuotientGroup.mk (frame * swapFirstTwo) : Flags .line) =
      QuotientGroup.mk (frame * Adelic.weyl) := by
  apply QuotientGroup.eq.mpr
  simp only [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  change InLineParabolic (swapFirstTwo⁻¹ * Adelic.weyl)
  constructor <;> simp [swapFirstTwo, Adelic.weyl,
    Matrix.mul_apply, Fin.sum_univ_three]

theorem weyl_cubed : (Adelic.weyl : RationalGL3) ^ 3 = 1 := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Adelic.weyl, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem chainBoundary_apartment (frame : RationalGL3) :
    chainBoundary (apartment frame) = 0 := by
  simp only [apartment, map_add, map_sub, chainBoundary_single, one_smul, endpoint_mk,
    plane_swapFirstTwo, line_swapFirstTwo]
  have square : frame * Adelic.weyl * Adelic.weyl = frame * Adelic.weyl ^ 2 := by
    simp [pow_two, mul_assoc]
  have cube : frame * Adelic.weyl ^ 2 * Adelic.weyl = frame := by
    rw [mul_assoc, ← pow_succ, weyl_cubed, mul_one]
  rw [square, cube]
  abel

theorem goodChains_single (edge : Edges) (coefficient : ℂ) (good : edge ∈ goodEdges) :
    Finsupp.single edge coefficient ∈ goodChains := by
  rw [mem_goodChains]
  intro candidate supported
  have equality := (Finsupp.mem_support_single candidate edge coefficient).mp supported
  exact equality.1 ▸ good

theorem goodChains_apartment (frame : RationalGL3)
    (good : ∀ column : Fin 3,
      GoodFlag .line (QuotientGroup.mk (frame * Adelic.weyl ^ column.val)))
    (goodPlane : ∀ column : Fin 3,
      GoodFlag .plane (QuotientGroup.mk (frame * Adelic.weyl ^ column.val))) :
    apartment frame ∈ goodChains := by
  have original : ∀ column : Fin 3,
      Finsupp.single (QuotientGroup.mk (frame * Adelic.weyl ^ column.val)) (1 : ℂ) ∈
        goodChains := by
    intro column
    apply goodChains_single
    exact ⟨goodPlane column, good column⟩
  have swapped : ∀ column : Fin 3,
      Finsupp.single (QuotientGroup.mk (frame * Adelic.weyl ^ column.val * swapFirstTwo))
        (1 : ℂ) ∈ goodChains := by
    intro column
    apply goodChains_single
    change GoodFlag .plane
        (QuotientGroup.mk (frame * Adelic.weyl ^ column.val * swapFirstTwo)) ∧
      GoodFlag .line (QuotientGroup.mk (frame * Adelic.weyl ^ column.val * swapFirstTwo))
    rw [plane_swapFirstTwo, line_swapFirstTwo]
    constructor
    · exact goodPlane column
    · fin_cases column
      · simpa using good 1
      · simpa [pow_two, mul_assoc] using good 2
      · simpa [mul_assoc, ← pow_succ, weyl_cubed] using good 0
  have first := goodChains.sub_mem (original 0) (swapped 0)
  have second := goodChains.sub_mem (original 1) (swapped 1)
  have third := goodChains.sub_mem (original ⟨2, by decide⟩) (swapped ⟨2, by decide⟩)
  simpa only [apartment, Fin.val_zero, Fin.val_one, Fin.val_mk, pow_zero, pow_one, mul_one,
    add_sub_assoc] using goodChains.add_mem (goodChains.add_mem first second) third

theorem goodFlag_column (frame : IntegralGL3) (side : Side) (column : Fin 3)
    (allowed : match side with
      | .plane => column ≠ 2
      | .line => column = 0)
    (nonzero : (frame.val 2 column : ZMod 3) ≠ 0) :
    GoodFlag side (QuotientGroup.mk
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) frame)) := by
  refine ⟨fun row => frame.val row column, ?_, nonzero⟩
  refine ⟨Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) frame, rfl,
    Pi.single column 1, ?_, ?_⟩
  · cases side with
    | plane => simp [allowed]
    | line => subst column; simp
  · funext row
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]

def integralWeyl : IntegralGL3 := Adelic.weyl

theorem integralWeyl_rational :
    Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) integralWeyl = Adelic.weyl := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> rfl

theorem normalized_rotated_frame (frame : IntegralGL3)
    (normalized : ∀ column : Fin 3, (frame.val 2 column : ZMod 3) = 1)
    (rotation : Fin 3) :
    ∀ column : Fin 3,
      ((frame * integralWeyl ^ rotation.val).val 2 column : ZMod 3) = 1 := by
  intro column
  fin_cases rotation <;> fin_cases column <;>
    simp [integralWeyl, Adelic.weyl, pow_succ, Matrix.mul_apply,
      Fin.sum_univ_three, normalized]

theorem normalized_apartment_goodCycle (frame : IntegralGL3)
    (normalized : ∀ column : Fin 3, (frame.val 2 column : ZMod 3) = 1) :
    GoodCycle (apartment (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) frame)) := by
  refine ⟨chainBoundary_apartment _, (mem_goodChains _).mp ?_⟩
  apply goodChains_apartment
  · intro rotation
    have nonzero : (((frame * integralWeyl ^ rotation.val).val 2 0 : ℤ) : ZMod 3) ≠ 0 := by
      rw [normalized_rotated_frame frame normalized rotation 0]
      exact one_ne_zero
    simpa [map_mul, map_pow, integralWeyl_rational] using
      goodFlag_column (frame * integralWeyl ^ rotation.val) .line 0 rfl nonzero
  · intro rotation
    have nonzero : (((frame * integralWeyl ^ rotation.val).val 2 0 : ℤ) : ZMod 3) ≠ 0 := by
      rw [normalized_rotated_frame frame normalized rotation 0]
      exact one_ne_zero
    simpa [map_mul, map_pow, integralWeyl_rational] using
      goodFlag_column (frame * integralWeyl ^ rotation.val) .plane 0 (by decide) nonzero

theorem integralLevel_lastRow (groupElement : arithmeticLevel) (column : Fin 3) :
    (groupElement.val.val 2 column : ZMod 3) = lastRow column := by
  have rowEquality :
      lastRow ᵥ* (reductionThree groupElement.val).val = lastRow := groupElement.property
  simpa [lastRow, Matrix.vecMul, dotProduct, Pi.single_apply, reductionThree] using
    congrFun rowEquality column

theorem integralLevel_lastCoordinate (groupElement : arithmeticLevel) (vector : Fin 3 → ℤ) :
    ((groupElement.val.val *ᵥ vector) 2 : ZMod 3) = (vector 2 : ZMod 3) := by
  simp [Matrix.mulVec, dotProduct, Int.cast_sum, integralLevel_lastRow, lastRow,
    Pi.single_apply]

theorem integralVectorInFlag_translate (groupElement : arithmeticLevel) (side : Side)
    (flag : Flags side) (vector : Fin 3 → ℤ)
    (membership : IntegralVectorInFlag side flag vector) :
    IntegralVectorInFlag side (rationalInclusion groupElement • flag)
      (groupElement.val.val *ᵥ vector) := by
  obtain ⟨frame, equality, coordinates, allowed, equation⟩ := membership
  refine ⟨rationalInclusion groupElement * frame, ?_, coordinates, ?_, ?_⟩
  · rw [← equality]
    rfl
  · cases side <;> exact allowed
  · rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, equation]
    funext row
    simp [rationalInclusion, Matrix.mulVec, dotProduct]

theorem goodFlag_translate_integral (groupElement : arithmeticLevel) (side : Side)
    (flag : Flags side) (good : GoodFlag side flag) :
    GoodFlag side (rationalInclusion groupElement • flag) := by
  obtain ⟨vector, membership, nonzero⟩ := good
  refine ⟨groupElement.val.val *ᵥ vector,
    integralVectorInFlag_translate groupElement side flag vector membership, ?_⟩
  rwa [integralLevel_lastCoordinate]

theorem goodFlag_translate (groupElement : rationalLevel) (side : Side)
    (flag : Flags side) (good : GoodFlag side flag) :
    GoodFlag side (groupElement.val • flag) := by
  obtain ⟨integral, equality⟩ := MonoidHom.mem_range.mp groupElement.property
  rw [← equality]
  exact goodFlag_translate_integral integral side flag good

theorem goodChain_translate (groupElement : rationalLevel) (chain : EdgeChains)
    (good : GoodChain chain) : GoodChain (translateChain groupElement.val chain) := by
  classical
  intro edge supported
  have imageMembership := Finsupp.mapDomain_support supported
  obtain ⟨original, originalSupported, equality⟩ := Finset.mem_image.mp imageMembership
  subst edge
  rw [endpoint_smul, endpoint_smul]
  exact ⟨goodFlag_translate groupElement .plane _ (good original originalSupported).1,
    goodFlag_translate groupElement .line _ (good original originalSupported).2⟩

def translateVertices (groupElement : RationalGL3) : VertexChains →ₗ[ℂ] VertexChains :=
  Finsupp.lmapDomain ℂ ℂ (translateVertex groupElement)

theorem chainBoundary_translate (groupElement : RationalGL3) (chain : EdgeChains) :
    chainBoundary (translateChain groupElement chain) =
      translateVertices groupElement (chainBoundary chain) := by
  have equality : chainBoundary.comp (translateChain groupElement) =
      (translateVertices groupElement).comp chainBoundary := by
    apply Finsupp.lhom_ext
    intro edge coefficient
    simp only [LinearMap.comp_apply, translateChain_single, chainBoundary_single,
      map_smul, map_sub, endpoint_smul]
    simp [translateVertices, translateVertex]
  exact LinearMap.congr_fun equality chain

theorem goodCycle_translate (groupElement : rationalLevel) (chain : EdgeChains)
    (good : GoodCycle chain) : GoodCycle (translateChain groupElement.val chain) := by
  constructor
  · rw [chainBoundary_translate, good.1, map_zero]
  · exact goodChain_translate groupElement chain good.2

def goodCycleAction : Representation ℂ rationalLevel goodCycles :=
  let chainAction : Representation ℂ rationalLevel EdgeChains :=
    { toFun := fun groupElement => translateChain groupElement.val
      map_one' := by
        ext edge coefficient
        simp [translateChain_single]
      map_mul' := by
        intro first second
        ext edge coefficient
        simp [translateChain_single, Module.End.mul_apply, mul_smul] }
  chainAction.subrepresentation goodCycles (by
    intro groupElement chain membership
    exact (mem_goodCycles _).mpr
      (goodCycle_translate groupElement chain ((mem_goodCycles _).mp membership)))

abbrev NormalizedFrames :=
  {frame : IntegralGL3 // ∀ column : Fin 3, (frame.val 2 column : ZMod 3) = 1}

def normalizedApartment (frame : NormalizedFrames) : goodCycles :=
  ⟨apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) frame.val),
    (mem_goodCycles _).mpr (normalized_apartment_goodCycle frame.val frame.property)⟩

def apartmentPresentation : (NormalizedFrames →₀ ℂ) →ₗ[ℂ] goodCycles :=
  Finsupp.linearCombination ℂ normalizedApartment

def normalizedFrameEvaluation {n : ℕ} (polynomial : HomogeneousPoly n)
    (frame : NormalizedFrames) : HomogeneousPoly n :=
  homogeneousAction n (-1)
    (GeneralLinearGroup.map (Int.castRingHom ℂ) frame.val) polynomial

def frameEvaluation {n : ℕ} (polynomial : HomogeneousPoly n) :
    (NormalizedFrames →₀ ℂ) →ₗ[ℂ] HomogeneousPoly n :=
  Finsupp.linearCombination ℂ (normalizedFrameEvaluation polynomial)

theorem normalizedFrameEvaluation_coe {n : ℕ} (polynomial : HomogeneousPoly n)
    (frame : NormalizedFrames) :
    (normalizedFrameEvaluation polynomial frame).val =
      MvPolynomial.C ((GeneralLinearGroup.det frame.val : ℤ) : ℂ) *
        substitute (GeneralLinearGroup.map (Int.castRingHom ℂ) frame.val)⁻¹.val
          polynomial.val := by
  change action (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) frame.val)
      polynomial.val = _
  rw [action_apply]
  have character : determinantCharacter (-1)
      (GeneralLinearGroup.map (Int.castRingHom ℂ) frame.val) =
      ((GeneralLinearGroup.det frame.val : ℤ) : ℂ) := by
    simp only [determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
      GeneralLinearGroup.map_det]
    rcases Int.units_eq_one_or (GeneralLinearGroup.det frame.val) with positive | negative
    · rw [positive]; simp
    · rw [negative]; simp
  rw [character, Algebra.smul_def]
  rfl

def translateNormalizedFrame (groupElement : arithmeticLevel)
    (frame : NormalizedFrames) : NormalizedFrames :=
  ⟨groupElement.val * frame.val, by
    intro column
    have equality := integralLevel_lastCoordinate groupElement (fun row => frame.val.val row column)
    simpa [Matrix.mulVec, Matrix.mul_apply, dotProduct, frame.property] using equality⟩

theorem normalizedApartment_translate (groupElement : arithmeticLevel)
    (frame : NormalizedFrames) :
    (normalizedApartment (translateNormalizedFrame groupElement frame)).val =
      translateChain (rationalInclusion groupElement) (normalizedApartment frame).val := by
  simp only [normalizedApartment, translateNormalizedFrame, map_mul,
    translateChain_apartment]
  rfl

theorem normalizedFrameEvaluation_translate {n : ℕ} (polynomial : HomogeneousPoly n)
    (groupElement : arithmeticLevel) (frame : NormalizedFrames) :
    normalizedFrameEvaluation polynomial (translateNormalizedFrame groupElement frame) =
      homogeneousAction n (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) groupElement.val)
        (normalizedFrameEvaluation polynomial frame) := by
  simp [normalizedFrameEvaluation, translateNormalizedFrame, map_mul,
    Module.End.mul_apply]

theorem zero_polynomial_functional (n : ℕ) :
    IsPolynomialFunctional (0 : HomogeneousPoly n)
      (0 : EdgeChains →ₗ[ℂ] HomogeneousPoly n) := by
  constructor
  · intro groupElement chain _cycle
    simp
  · intro frame _normalized
    simp

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers
