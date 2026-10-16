module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.FlagGeometry
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralBases

noncomputable section

theorem basis_snf_scalar_ne_zero {lattice : Submodule ℤ (Fin 3 → ℤ)}
    {dimension : ℕ} (normalForm : Module.Basis.SmithNormalForm lattice (Fin 3) dimension)
    (index : Fin dimension) : normalForm.a index ≠ 0 := by
  intro zero
  have equation := normalForm.snf index
  rw [zero, zero_smul] at equation
  apply normalForm.bN.ne_zero index
  apply Subtype.ext
  exact equation

theorem saturated_lattice_has_adapted_basis (lattice : Submodule ℤ (Fin 3 → ℤ))
    (saturated : ∀ scalar : ℤ, scalar ≠ 0 → ∀ vector : Fin 3 → ℤ,
      scalar • vector ∈ lattice → vector ∈ lattice) :
    ∃ (basis : Module.Basis (Fin 3) ℤ (Fin 3 → ℤ)) (dimension : ℕ)
      (indices : Fin dimension ↪ Fin 3),
      lattice = Submodule.span ℤ (Set.range (fun index => basis (indices index))) := by
  obtain ⟨dimension, normalForm⟩ := lattice.smithNormalForm (Pi.basisFun ℤ (Fin 3))
  refine ⟨normalForm.bM, dimension, normalForm.f, ?_⟩
  have selected_mem (index : Fin dimension) : normalForm.bM (normalForm.f index) ∈ lattice := by
    apply saturated (normalForm.a index) (basis_snf_scalar_ne_zero normalForm index)
    rw [← normalForm.snf]
    exact (normalForm.bN index).property
  apply le_antisymm
  · intro vector membership
    have reconstruction := congrArg Subtype.val (normalForm.bN.sum_repr ⟨vector, membership⟩)
    change (∑ index, (normalForm.bN.repr ⟨vector, membership⟩) index •
      normalForm.bN index).val = vector at reconstruction
    simp only [Submodule.coe_sum, Submodule.coe_smul] at reconstruction
    rw [← reconstruction]
    apply Submodule.sum_mem
    intro index _supported
    apply Submodule.smul_mem
    rw [normalForm.snf]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨index, rfl⟩
  · apply Submodule.span_le.mpr
    rintro vector ⟨index, rfl⟩
    exact selected_mem index

theorem integralFlagLattice_has_adapted_basis (side : Side) (flag : Flags side) :
    ∃ (basis : Module.Basis (Fin 3) ℤ (Fin 3 → ℤ)) (dimension : ℕ)
      (indices : Fin dimension ↪ Fin 3),
      integralFlagLattice side flag =
        Submodule.span ℤ (Set.range (fun index => basis (indices index))) := by
  apply saturated_lattice_has_adapted_basis
  intro scalar nonzero vector membership
  exact (integralFlagLattice_saturated side flag scalar nonzero vector).mp membership

theorem rationalVector_has_integral_multiple (vector : Fin 3 → ℚ) :
    ∃ (scalar : ℤ) (integral : Fin 3 → ℤ), scalar ≠ 0 ∧
      (scalar : ℚ) • vector = integerVectorMap integral := by
  obtain ⟨denominator, integralCoordinates⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) vector
  choose integral equality using integralCoordinates
  refine ⟨denominator.val, integral, mem_nonZeroDivisors_iff_ne_zero.mp denominator.property, ?_⟩
  ext index
  exact (equality index).symm

theorem rational_span_integralFlagLattice (side : Side) (flag : Flags side) :
    Submodule.span ℚ (integerVectorMap '' (integralFlagLattice side flag : Set (Fin 3 → ℤ))) =
      flagSubspace side flag := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro vector ⟨integral, membership, rfl⟩
    exact membership
  · intro vector membership
    obtain ⟨scalar, integral, nonzero, equality⟩ := rationalVector_has_integral_multiple vector
    have integralMembership : integral ∈ integralFlagLattice side flag := by
      change integerVectorMap integral ∈ flagSubspace side flag
      rw [← equality]
      exact (flagSubspace side flag).smul_mem (scalar : ℚ) membership
    have spanMembership : (scalar : ℚ) • vector ∈
        Submodule.span ℚ (integerVectorMap ''
          (integralFlagLattice side flag : Set (Fin 3 → ℤ))) := by
      rw [equality]
      exact Submodule.subset_span ⟨integral, integralMembership, rfl⟩
    exact ((Submodule.span ℚ (integerVectorMap ''
      (integralFlagLattice side flag : Set (Fin 3 → ℤ)))).smul_mem_iff
        (Int.cast_ne_zero.mpr nonzero : (scalar : ℚ) ≠ 0)).mp spanMembership

def integralFrameOfBasis (basis : Module.Basis (Fin 3) ℤ (Fin 3 → ℤ)) : IntegralGL3 :=
  GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv ((Pi.basisFun ℤ (Fin 3)).equiv basis
      (Equiv.refl (Fin 3))))

theorem integralFrameOfBasis_column (basis : Module.Basis (Fin 3) ℤ (Fin 3 → ℤ))
    (column : Fin 3) : (integralFrameOfBasis basis).val.col column = basis column := by
  have evaluation : (GeneralLinearGroup.toLin (integralFrameOfBasis basis)) •
      (Pi.basisFun ℤ (Fin 3)) column = basis column := by
    simp only [integralFrameOfBasis, MulEquiv.apply_symm_apply,
      LinearMap.GeneralLinearGroup.ofLinearEquiv_smul]
    exact Module.Basis.equiv_apply _ column basis (Equiv.refl (Fin 3))
  change (GeneralLinearGroup.toLin (integralFrameOfBasis basis)).toLinearEquiv
    ((Pi.basisFun ℤ (Fin 3)) column) = basis column at evaluation
  rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv, GeneralLinearGroup.toLin_apply,
    Pi.basisFun_apply] at evaluation
  change (integralFrameOfBasis basis).val *ᵥ Pi.single column 1 = basis column at evaluation
  rwa [Matrix.mulVec_single_one] at evaluation

def rationalBasisOfIntegral (basis : Module.Basis (Fin 3) ℤ (Fin 3 → ℤ)) :
    Module.Basis (Fin 3) ℚ (Fin 3 → ℚ) :=
  (Pi.basisFun ℚ (Fin 3)).map
    (matrixVectorEquiv (GeneralLinearGroup.map (Int.castRingHom ℚ) (integralFrameOfBasis basis)))

theorem rationalBasisOfIntegral_apply (basis : Module.Basis (Fin 3) ℤ (Fin 3 → ℤ))
    (column : Fin 3) : rationalBasisOfIntegral basis column = integerVectorMap (basis column) := by
  rw [rationalBasisOfIntegral, Module.Basis.map_apply, Pi.basisFun_apply]
  change (GeneralLinearGroup.map (Int.castRingHom ℚ) (integralFrameOfBasis basis)).val *ᵥ
    Pi.single column 1 = integerVectorMap (basis column)
  rw [Matrix.mulVec_single_one]
  ext row
  exact congrArg (fun vector : Fin 3 → ℤ => (vector row : ℚ))
    (integralFrameOfBasis_column basis column)

theorem rational_span_integer_span {indices : Type*} (vectors : indices → (Fin 3 → ℤ)) :
    Submodule.span ℚ (integerVectorMap ''
      (Submodule.span ℤ (Set.range vectors) : Set (Fin 3 → ℤ))) =
      Submodule.span ℚ (Set.range (fun index => integerVectorMap (vectors index))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro vector ⟨integral, membership, rfl⟩
    induction membership using Submodule.span_induction with
    | mem integral membership =>
      obtain ⟨index, rfl⟩ := membership
      exact Submodule.subset_span ⟨index, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add first second _firstMem _secondMem firstSpan secondSpan =>
      rw [map_add]
      exact Submodule.add_mem _ firstSpan secondSpan
    | smul scalar integral _membership spanMembership =>
      rw [map_smul]
      change (scalar : ℚ) • integerVectorMap integral ∈ _
      exact Submodule.smul_mem _ (scalar : ℚ) spanMembership
  · apply Submodule.span_le.mpr
    rintro vector ⟨index, rfl⟩
    exact Submodule.subset_span ⟨vectors index, Submodule.subset_span ⟨index, rfl⟩, rfl⟩

theorem adaptedBasis_dimension (side : Side) (flag : Flags side)
    (basis : Module.Basis (Fin 3) ℤ (Fin 3 → ℤ)) (dimension : ℕ)
    (indices : Fin dimension ↪ Fin 3)
    (adapted : integralFlagLattice side flag =
      Submodule.span ℤ (Set.range (fun index => basis (indices index)))) :
    dimension = match side with | .plane => 2 | .line => 1 := by
  have rationalSpan := rational_span_integralFlagLattice side flag
  rw [adapted, rational_span_integer_span] at rationalSpan
  have independent : LinearIndependent ℚ
      (fun index => integerVectorMap (basis (indices index))) := by
    have functionEquality : (rationalBasisOfIntegral basis) ∘ indices =
        (fun index => integerVectorMap (basis (indices index))) := by
      funext index
      exact rationalBasisOfIntegral_apply basis (indices index)
    rw [← functionEquality]
    exact (rationalBasisOfIntegral basis).linearIndependent.comp indices indices.injective
  have rank := finrank_span_eq_card independent
  rw [rationalSpan, flagSubspace_finrank, Fintype.card_fin] at rank
  cases side <;> exact rank.symm

theorem integralFlagLattice_adapted_basis_rank (side : Side) (flag : Flags side) :
    ∃ (basis : Module.Basis (Fin 3) ℤ (Fin 3 → ℤ))
      (indices : Fin (match side with | .plane => 2 | .line => 1) ↪ Fin 3),
      integralFlagLattice side flag =
        Submodule.span ℤ (Set.range (fun index => basis (indices index))) := by
  obtain ⟨basis, dimension, indices, adapted⟩ := integralFlagLattice_has_adapted_basis side flag
  have rank := adaptedBasis_dimension side flag basis dimension indices adapted
  cases side <;> simp only at rank ⊢ <;> subst dimension <;> exact ⟨basis, indices, adapted⟩

theorem line_lattice_basis (flag : Flags .line) :
    ∃ basis : Module.Basis (Fin 3) ℤ (Fin 3 → ℤ),
      integralFlagLattice .line flag = Submodule.span ℤ {basis 0} := by
  obtain ⟨basis, indices, adapted⟩ := integralFlagLattice_adapted_basis_rank .line flag
  let reordered := basis.reindex (Equiv.swap (0 : Fin 3) (indices 0))
  refine ⟨reordered, ?_⟩
  rw [adapted, Set.range_unique]
  have first : reordered 0 = basis (indices 0) := by
    simp [reordered, Module.Basis.reindex_apply]
  rw [first]
  rfl

theorem good_line_basis (flag : Flags .line) (good : GoodFlag .line flag) :
    ∃ basis : Module.Basis (Fin 3) ℤ (Fin 3 → ℤ),
      integralFlagLattice .line flag = Submodule.span ℤ {basis 0} ∧
      ((basis 0) 2 : ZMod 3) ≠ 0 := by
  obtain ⟨basis, adapted⟩ := line_lattice_basis flag
  refine ⟨basis, adapted, ?_⟩
  rw [goodFlag_iff_lattice] at good
  obtain ⟨vector, membership, nonzero⟩ := good
  rw [adapted] at membership
  obtain ⟨scalar, equality⟩ := Submodule.mem_span_singleton.mp membership
  intro zero
  apply nonzero
  rw [← equality]
  change ((scalar * (basis 0) 2 : ℤ) : ZMod 3) = 0
  rw [Int.cast_mul, zero, mul_zero]

theorem line_frame_subspace (frame : RationalGL3) :
    frameSubspace .line frame = Submodule.span ℚ {frame.val.col 0} := by
  ext vector
  rw [mem_frameSubspace, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨coordinates, allowed, equation⟩
    refine ⟨coordinates 0, ?_⟩
    rw [← equation]
    ext row
    simp [standardSubspace] at allowed
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, allowed.1, allowed.2,
      Matrix.col, mul_comm]
  · rintro ⟨scalar, equality⟩
    refine ⟨![scalar, 0, 0], ⟨rfl, rfl⟩, ?_⟩
    rw [← equality]
    ext row
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.col, mul_comm]

theorem good_line_integral_frame (flag : Flags .line) (good : GoodFlag .line flag) :
    ∃ frame : IntegralGL3,
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) frame) : Flags .line) = flag ∧
      (frame.val 2 0 : ZMod 3) ≠ 0 := by
  obtain ⟨basis, adapted, nonzero⟩ := good_line_basis flag good
  refine ⟨integralFrameOfBasis basis, ?_, ?_⟩
  · apply flagSubspace_injective
    rw [flagSubspace_mk, line_frame_subspace,
      ← rational_span_integralFlagLattice .line flag, adapted]
    have singleton := rational_span_integer_span (fun _index : Fin 1 => basis 0)
    simp only [Set.range_unique] at singleton
    rw [singleton]
    have columnEquality :
        (GeneralLinearGroup.map (Int.castRingHom ℚ) (integralFrameOfBasis basis)).val.col 0 =
          integerVectorMap (basis 0) := by
      ext row
      exact congrArg (fun vector : Fin 3 → ℤ => (vector row : ℚ))
        (integralFrameOfBasis_column basis 0)
    rw [columnEquality]
  · have columnEquality := congrArg (fun vector : Fin 3 → ℤ => (vector 2 : ZMod 3))
      (integralFrameOfBasis_column basis 0)
    exact columnEquality ▸ nonzero

def firstColumnSign : IntegralGL3 :=
  ⟨!![-1,0,0;0,1,0;0,0,1], !![-1,0,0;0,1,0;0,0,1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem nonzero_modThree_sign (value : ZMod 3) (nonzero : value ≠ 0) :
    value = 1 ∨ value = -1 := by
  fin_cases value
  · exact False.elim (nonzero rfl)
  · exact Or.inl rfl
  · exact Or.inr (show (2 : ZMod 3) = -1 from rfl)

theorem signed_line_integral_frame (flag : Flags .line) (good : GoodFlag .line flag) :
    ∃ frame : IntegralGL3,
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) frame) : Flags .line) = flag ∧
      (frame.val 2 0 : ZMod 3) = 1 := by
  obtain ⟨frame, equality, nonzero⟩ := good_line_integral_frame flag good
  rcases nonzero_modThree_sign (frame.val 2 0 : ZMod 3) nonzero with positive | negative
  · exact ⟨frame, equality, positive⟩
  · refine ⟨frame * firstColumnSign, ?_, ?_⟩
    · rw [map_mul, QuotientGroup.mk_mul_of_mem]
      · exact equality
      · change InLineParabolic (GeneralLinearGroup.map (Int.castRingHom ℚ) firstColumnSign)
        exact ⟨rfl, rfl⟩
    · simp [Matrix.mul_apply, Fin.sum_univ_three, firstColumnSign, negative]

theorem normalized_line_integral_frame (flag : Flags .line) (good : GoodFlag .line flag) :
    ∃ frame : TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers.NormalizedFrames,
      (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) frame.val) : Flags .line) =
        flag := by
  obtain ⟨frame, equality, normalized⟩ := signed_line_integral_frame flag good
  let firstShear : ℤ := (1 - (frame.val 2 1 : ZMod 3)).val
  let secondShear : ℤ := (1 - (frame.val 2 2 : ZMod 3)).val
  have firstCast : (firstShear : ZMod 3) = 1 - (frame.val 2 1 : ZMod 3) := by
    simp [firstShear]
  have secondCast : (secondShear : ZMod 3) = 1 - (frame.val 2 2 : ZMod 3) := by
    simp [secondShear]
  refine ⟨⟨frame * Adelic.upperUnipotent firstShear secondShear, ?_⟩, ?_⟩
  · intro column
    fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Adelic.upperUnipotent,
        normalized, firstCast, secondCast]
  · rw [map_mul, QuotientGroup.mk_mul_of_mem]
    · exact equality
    · change InLineParabolic (GeneralLinearGroup.map (Int.castRingHom ℚ)
        (Adelic.upperUnipotent firstShear secondShear))
      exact ⟨rfl, rfl⟩

theorem good_line_arithmetic_orbit (flag : Flags .line) (good : GoodFlag .line flag) :
    ∃ groupElement : arithmeticLevel,
      rationalInclusion groupElement •
        (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ)
          TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.referenceIntegral) : Flags .line) = flag := by
  obtain ⟨frame, equality⟩ := normalized_line_integral_frame flag good
  refine ⟨TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.frameToLevel frame, ?_⟩
  have cancellation := congrArg Subtype.val
    (TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.levelToFrame_frameToLevel frame)
  have frameEquality : (TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.frameToLevel frame).val *
      TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.referenceIntegral = frame.val := cancellation
  change (QuotientGroup.mk (rationalInclusion (TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.frameToLevel frame) *
    GeneralLinearGroup.map (Int.castRingHom ℚ) TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.referenceIntegral) :
      Flags .line) = flag
  have rationalEquality : rationalInclusion (TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.frameToLevel frame) *
      GeneralLinearGroup.map (Int.castRingHom ℚ) TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.referenceIntegral =
        GeneralLinearGroup.map (Int.castRingHom ℚ) frame.val := by
    change GeneralLinearGroup.map (Int.castRingHom ℚ)
      (TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.frameToLevel frame).val *
        GeneralLinearGroup.map (Int.castRingHom ℚ) TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.referenceIntegral = _
    rw [← map_mul, frameEquality]
  rw [rationalEquality]
  exact equality

theorem good_lines_transitive (first second : Flags .line)
    (firstGood : GoodFlag .line first) (secondGood : GoodFlag .line second) :
    ∃ groupElement : arithmeticLevel, rationalInclusion groupElement • first = second := by
  obtain ⟨firstGroup, firstEquality⟩ := good_line_arithmetic_orbit first firstGood
  obtain ⟨secondGroup, secondEquality⟩ := good_line_arithmetic_orbit second secondGood
  refine ⟨secondGroup * firstGroup⁻¹, ?_⟩
  rw [map_mul, map_inv, ← firstEquality, mul_smul, inv_smul_smul, secondEquality]

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralBases
