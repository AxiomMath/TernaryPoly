module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.RationalRelations

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry TernaryPeriodPolynomials.GoodApartmentFunctional.Incidence
open TernaryPeriodPolynomials.GoodApartmentFunctional.Presentation TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralReduction
open TernaryPeriodPolynomials.GoodApartmentFunctional.RationalApartments
open TernaryPeriodPolynomials.GoodApartmentFunctional.ApartmentGeneration

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralSymbols

noncomputable section

abbrev SymbolSpace := (NormalizedFrames →₀ ℂ) ⧸ presentationRelations

def frameSymbol (frame : NormalizedFrames) : SymbolSpace :=
  presentationRelations.mkQ (Finsupp.single frame 1)

theorem frameSymbol_cycle (frame : NormalizedFrames) :
    frameSymbol (rightCycleFrame frame) = frameSymbol frame := by
  have membership : cycleRelation frame ∈ presentationRelations :=
    Submodule.subset_span (Or.inl (Or.inr ⟨frame, rfl⟩))
  have zero : presentationRelations.mkQ (cycleRelation frame) = 0 :=
    (Submodule.Quotient.mk_eq_zero presentationRelations).mpr membership
  simpa only [cycleRelation, map_sub, frameSymbol, sub_eq_zero] using zero

theorem frameSymbol_swap (frame : NormalizedFrames) :
    frameSymbol (rightSwapFrame frame) = -frameSymbol frame := by
  have membership : swapRelation frame ∈ presentationRelations :=
    Submodule.subset_span (Or.inr ⟨frame, rfl⟩)
  have zero : presentationRelations.mkQ (swapRelation frame) = 0 :=
    (Submodule.Quotient.mk_eq_zero presentationRelations).mpr membership
  have addition : frameSymbol (rightSwapFrame frame) + frameSymbol frame = 0 := by
    simpa only [swapRelation, map_add, frameSymbol] using zero
  exact eq_neg_of_add_eq_zero_left addition

theorem frameSymbol_norm (frame : NormalizedFrames) :
    frameSymbol frame + frameSymbol (rightNormFrame frame) +
      frameSymbol (rightNormFrame (rightNormFrame frame)) = 0 := by
  have membership : normRelation frame ∈ presentationRelations :=
    Submodule.subset_span (Or.inl (Or.inl ⟨frame, rfl⟩))
  have zero : presentationRelations.mkQ (normRelation frame) = 0 :=
    (Submodule.Quotient.mk_eq_zero presentationRelations).mpr membership
  simpa only [normRelation, map_add, frameSymbol] using zero

theorem normalizedFrames_eq_of_columnLines_eq (first second : NormalizedFrames)
    (columns : ∀ column,
      columnLine (GeneralLinearGroup.map (Int.castRingHom ℚ) first.val) column =
        columnLine (GeneralLinearGroup.map (Int.castRingHom ℚ) second.val) column) :
    first = second := by
  classical
  let rationalFirst := GeneralLinearGroup.map (Int.castRingHom ℚ) first.val
  let rationalSecond := GeneralLinearGroup.map (Int.castRingHom ℚ) second.val
  have membership (column : Fin 3) : rationalSecond.val.col column ∈
      Submodule.span ℚ {rationalFirst.val.col column} := by
    rw [← columnLine_subspace, columns, columnLine_subspace]
    exact Submodule.mem_span_singleton_self _
  choose scalar scalarEquality using
    fun column => Submodule.mem_span_singleton.mp (membership column)
  let changeFrame : IntegralGL3 := first.val⁻¹ * second.val
  have changeColumn (column : Fin 3) :
      (GeneralLinearGroup.map (Int.castRingHom ℚ) changeFrame).val.col column =
        scalar column • Pi.single column 1 := by
    have changeEquality : GeneralLinearGroup.map (Int.castRingHom ℚ) changeFrame =
        rationalFirst⁻¹ * rationalSecond := by
      simp [changeFrame, rationalFirst, rationalSecond]
    rw [changeEquality, ← Matrix.mulVec_single_one, GeneralLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one, ← scalarEquality column,
      Matrix.mulVec_smul, ← Matrix.mulVec_single_one, inverse_mulVec_mulVec]
  have diagonalEquality : changeFrame.val =
      Matrix.diagonal (fun column => changeFrame.val column column) := by
    ext row column
    by_cases equality : row = column
    · subst row
      simp
    · have entry := congrFun (changeColumn column) row
      change (changeFrame.val row column : ℚ) =
        scalar column * (Pi.single column 1 : Fin 3 → ℚ) row at entry
      simp [Ne.symm equality] at entry
      rw [Matrix.diagonal_apply_ne _ equality]
      exact Int.cast_injective entry
  have diagonalOne (column : Fin 3) : changeFrame.val column column = 1 := by
    have matrixUnit := changeFrame.isUnit
    rw [diagonalEquality] at matrixUnit
    have unit : IsUnit (changeFrame.val column column) :=
      Pi.isUnit_iff.mp (Matrix.isUnit_diagonal.mp matrixUnit) column
    have product : second.val.val = first.val.val * changeFrame.val := by
      change second.val.val = (first.val * changeFrame).val
      simp [changeFrame]
    have lastEntry := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℤ =>
      (matrix 2 column : ZMod 3)) product
    rw [diagonalEquality, Matrix.mul_diagonal, Int.cast_mul,
      first.property, second.property, one_mul] at lastEntry
    rcases Int.isUnit_iff.mp unit with positive | negative
    · exact positive
    · rw [negative] at lastEntry
      exact ((by decide : (1 : ZMod 3) ≠ -1) lastEntry).elim
  have changeOne : changeFrame = 1 := by
    apply Units.ext
    rw [diagonalEquality]
    simp only [diagonalOne]
    rfl
  apply Subtype.ext
  have equality := congrArg (fun frame : IntegralGL3 => first.val * frame) changeOne
  simpa [changeFrame] using equality.symm

def integralSymbolPresentation : SymbolSpace →ₗ[ℂ] goodCycles :=
  presentationRelations.liftQ (R₂ := ℂ) (M₂ := goodCycles)
    (τ₁₂ := RingHom.id ℂ) apartmentPresentation presentationRelations_apartment

theorem integralSymbolPresentation_mkQ (combination : NormalizedFrames →₀ ℂ) :
    integralSymbolPresentation (presentationRelations.mkQ combination) =
      apartmentPresentation combination := by
  rfl

theorem integralSymbolPresentation_frameSymbol (frame : NormalizedFrames) :
    integralSymbolPresentation (frameSymbol frame) = normalizedApartment frame := by
  rw [frameSymbol, integralSymbolPresentation_mkQ]
  simp [apartmentPresentation]

theorem integralSymbolPresentation_surjective :
    Function.Surjective integralSymbolPresentation := by
  intro chain
  obtain ⟨combination, rfl⟩ := apartmentPresentation_surjective chain
  exact ⟨presentationRelations.mkQ combination, integralSymbolPresentation_mkQ combination⟩

theorem completeRelations_iff_injective :
    apartmentPresentation.ker ≤ presentationRelations ↔
      Function.Injective integralSymbolPresentation := by
  constructor
  · intro complete first second equality
    obtain ⟨firstCombination, rfl⟩ := presentationRelations.mkQ_surjective first
    obtain ⟨secondCombination, rfl⟩ := presentationRelations.mkQ_surjective second
    rw [integralSymbolPresentation_mkQ, integralSymbolPresentation_mkQ] at equality
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (Submodule.Quotient.mk_eq_zero presentationRelations).mpr
    apply complete
    change apartmentPresentation (firstCombination - secondCombination) = 0
    rw [map_sub, equality, sub_self]
  · intro injective combination membership
    apply (Submodule.Quotient.mk_eq_zero presentationRelations).mp
    apply injective
    change integralSymbolPresentation (presentationRelations.mkQ combination) =
      integralSymbolPresentation 0
    rw [integralSymbolPresentation_mkQ, map_zero]
    exact LinearMap.mem_ker.mp membership

def augmentedVector (frame : NormalizedFrames) : Fin 3 → ℤ :=
  -(frame.val.val.col 0 + frame.val.val.col 1)

theorem augmentedVector_normalized (frame : NormalizedFrames) :
    (augmentedVector frame 2 : ZMod 3) = 1 := by
  change ((-(frame.val.val 2 0 + frame.val.val 2 1) : ℤ) : ZMod 3) = 1
  push_cast
  rw [frame.property 0, frame.property 1]
  decide

def augmentedFirstFrame (frame : NormalizedFrames) : NormalizedFrames :=
  rightSwapFrame (rightNormFrame frame)

def augmentedSecondFrame (frame : NormalizedFrames) : NormalizedFrames :=
  rightSwapFrame (rightNormFrame (rightNormFrame frame))

theorem augmentedFirstFrame_matrix (frame : NormalizedFrames) :
    (augmentedFirstFrame frame).val.val =
      frame.val.val.updateCol 0 (augmentedVector frame) := by
  ext row column
  fin_cases column <;>
    simp [augmentedFirstFrame, rightSwapFrame, rightNormFrame,
      TernaryPeriodPolynomials.GoodApartmentFunctional.Relations.normMatrix, TernaryPeriodPolynomials.GoodApartmentFunctional.Relations.swapMatrix,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.updateCol, augmentedVector, Matrix.col,
      add_comm]

theorem augmentedSecondFrame_matrix (frame : NormalizedFrames) :
    (augmentedSecondFrame frame).val.val =
      frame.val.val.updateCol 1 (augmentedVector frame) := by
  ext row column
  fin_cases column <;>
    simp [augmentedSecondFrame, rightSwapFrame, rightNormFrame,
      TernaryPeriodPolynomials.GoodApartmentFunctional.Relations.normMatrix, TernaryPeriodPolynomials.GoodApartmentFunctional.Relations.swapMatrix,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.updateCol, augmentedVector, Matrix.col]
  ring

theorem frameSymbol_augmented (frame : NormalizedFrames) :
    frameSymbol frame = frameSymbol (augmentedFirstFrame frame) +
      frameSymbol (augmentedSecondFrame frame) := by
  rw [augmentedFirstFrame, augmentedSecondFrame, frameSymbol_swap, frameSymbol_swap]
  have norm := frameSymbol_norm frame
  rw [← neg_add]
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using norm)

def normalizedGoodRationalFrame (frame : NormalizedFrames) : GoodRationalFrames :=
  ⟨GeneralLinearGroup.map (Int.castRingHom ℚ) frame.val, by
      intro rotation
      change GoodFlag .line
        (QuotientGroup.mk (GeneralLinearGroup.map (Int.castRingHom ℚ) frame.val *
          Adelic.weyl ^ rotation.val))
      have nonzero : ((frame.val * integralWeyl ^ rotation.val).val 2 0 : ZMod 3) ≠ 0 := by
        rw [normalized_rotated_frame frame.val frame.property rotation 0]
        exact one_ne_zero
      simpa [map_mul, map_pow, integralWeyl_rational] using
        goodFlag_column (frame.val * integralWeyl ^ rotation.val) .line 0 rfl nonzero⟩

def normalizedFrameTriple (frame : NormalizedFrames) : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.Triples :=
  TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.rationalFrameTriple (normalizedGoodRationalFrame frame)

theorem normalizedFrameTriple_injective : Function.Injective normalizedFrameTriple := by
  intro first second equality
  apply normalizedFrames_eq_of_columnLines_eq
  intro column
  fin_cases column
  · exact congrArg (fun vertices : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.Triples => vertices.1.val) equality
  · exact congrArg (fun vertices : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.Triples => vertices.2.1.val) equality
  · exact congrArg (fun vertices : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.Triples => vertices.2.2.val) equality

def normalizedFramesToTriples : (NormalizedFrames →₀ ℂ) →ₗ[ℂ]
    TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.TripleChains :=
  Finsupp.linearCombination ℂ (fun frame => Finsupp.single (normalizedFrameTriple frame) 1)

theorem trianglePresentation_normalizedFramesToTriples (combination : NormalizedFrames →₀ ℂ) :
    TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.trianglePresentation (normalizedFramesToTriples combination) =
      apartmentPresentation combination := by
  have equality : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.trianglePresentation.comp normalizedFramesToTriples =
      apartmentPresentation := by
    apply Finsupp.lhom_ext
    intro frame coefficient
    rw [show Finsupp.single frame coefficient = coefficient • Finsupp.single frame 1 by simp]
    simp only [LinearMap.comp_apply, map_smul]
    congr 1
    apply Subtype.ext
    simp only [normalizedFramesToTriples, TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.trianglePresentation,
      Finsupp.linearCombination_single, one_smul, TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.tripleApartment,
      normalizedFrameTriple, TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.rationalFrameTriple,
      apartmentPresentation, normalizedApartment]
    exact (apartment_as_lineConnectors _ (normalizedGoodRationalFrame frame).property).symm
  exact LinearMap.congr_fun equality combination

theorem normalizedFramesToTriples_kernel (combination : NormalizedFrames →₀ ℂ) :
    normalizedFramesToTriples combination ∈ TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.rationalRelations ↔
      combination ∈ apartmentPresentation.ker := by
  rw [← TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.trianglePresentation_kernel, LinearMap.mem_ker,
    trianglePresentation_normalizedFramesToTriples, ← LinearMap.mem_ker]

theorem normalizedFramesToTriples_relations :
    presentationRelations ≤
      TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.rationalRelations.comap normalizedFramesToTriples := by
  intro combination membership
  exact (normalizedFramesToTriples_kernel combination).mpr
    (presentationRelations_apartment membership)

def integralToRationalSymbols : SymbolSpace →ₗ[ℂ] TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.RationalSymbols :=
  presentationRelations.liftQ (R₂ := ℂ) (M₂ := TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.RationalSymbols)
    (τ₁₂ := RingHom.id ℂ)
    (TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.rationalRelations.mkQ.comp normalizedFramesToTriples) (by
      intro combination membership
      change TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.rationalRelations.mkQ
        (normalizedFramesToTriples combination) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (normalizedFramesToTriples_relations membership))

theorem integralToRationalSymbols_mkQ (combination : NormalizedFrames →₀ ℂ) :
    integralToRationalSymbols (presentationRelations.mkQ combination) =
      TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.rationalRelations.mkQ (normalizedFramesToTriples combination) := by
  rfl

theorem integralToRationalSymbols_frameSymbol (frame : NormalizedFrames) :
    integralToRationalSymbols (frameSymbol frame) =
      TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.symbol (normalizedFrameTriple frame).1
        (normalizedFrameTriple frame).2.1 (normalizedFrameTriple frame).2.2 := by
  rw [frameSymbol, integralToRationalSymbols_mkQ]
  simp [normalizedFramesToTriples, TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.symbol,
    TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.triple]

theorem integralToRationalSymbols_surjective : Function.Surjective integralToRationalSymbols := by
  intro value
  obtain ⟨triples, rfl⟩ := TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.rationalRelations.mkQ_surjective value
  obtain ⟨combination, equality⟩ :=
    apartmentPresentation_surjective (TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.trianglePresentation triples)
  refine ⟨presentationRelations.mkQ combination, ?_⟩
  rw [integralToRationalSymbols_mkQ]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [← TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.trianglePresentation_kernel, LinearMap.mem_ker,
    map_sub, trianglePresentation_normalizedFramesToTriples, equality, sub_self]

theorem completeRelations_iff_rational_injective :
    apartmentPresentation.ker ≤ presentationRelations ↔
      Function.Injective integralToRationalSymbols := by
  constructor
  · intro complete first second equality
    obtain ⟨firstCombination, rfl⟩ := presentationRelations.mkQ_surjective first
    obtain ⟨secondCombination, rfl⟩ := presentationRelations.mkQ_surjective second
    rw [integralToRationalSymbols_mkQ, integralToRationalSymbols_mkQ] at equality
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (Submodule.Quotient.mk_eq_zero presentationRelations).mpr
    apply complete
    apply (normalizedFramesToTriples_kernel _).mp
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.rationalRelations.mkQ
      (normalizedFramesToTriples (firstCombination - secondCombination)) = 0
    rw [map_sub, map_sub, equality, sub_self]
  · intro injective combination membership
    apply (Submodule.Quotient.mk_eq_zero presentationRelations).mp
    apply injective
    change integralToRationalSymbols (presentationRelations.mkQ combination) =
      integralToRationalSymbols 0
    rw [integralToRationalSymbols_mkQ, map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      ((normalizedFramesToTriples_kernel combination).mpr membership)

theorem functional_of_rational_injective {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (solution : SymmetricSolution polynomial) (injective : Function.Injective integralToRationalSymbols) :
    ∃ extension : EdgeChains →ₗ[ℂ] HomogeneousPoly degree,
      IsPolynomialFunctional polynomial extension :=
  functional_of_complete_presentation polynomial solution apartmentPresentation_surjective
    (completeRelations_iff_rational_injective.mpr injective)

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralSymbols
