module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.IntegralSymbols

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers TernaryPeriodPolynomials.GoodApartmentFunctional.Presentation TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralSymbols
open TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry TernaryPeriodPolynomials.GoodApartmentFunctional.RationalApartments TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralReduction
open TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.FrameMoves

noncomputable section

theorem normalizedFrames_eq_of_matrix_eq (first second : NormalizedFrames)
    (equality : first.val.val = second.val.val) : first = second :=
  Subtype.ext (Units.ext equality)

theorem rightCycleFrame_entry (frame : NormalizedFrames) (row column : Fin 3) :
    (rightCycleFrame frame).val.val row column = frame.val.val row (column + 1) := by
  fin_cases column <;>
    simp [rightCycleFrame, integralWeyl, Adelic.weyl, Matrix.mul_apply, Fin.sum_univ_three]

theorem rightSwapFrame_entry (frame : NormalizedFrames) (row column : Fin 3) :
    (rightSwapFrame frame).val.val row column =
      frame.val.val row (Equiv.swap 0 1 column) := by
  fin_cases column <;>
    simp [rightSwapFrame, TernaryPeriodPolynomials.GoodApartmentFunctional.Relations.swapMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, Equiv.swap_apply_def]

theorem augmentedFirstFrame_entry (frame : NormalizedFrames) (row column : Fin 3) :
    (augmentedFirstFrame frame).val.val row column =
      if column = 0 then -(frame.val.val row 0 + frame.val.val row 1)
      else frame.val.val row column := by
  rw [augmentedFirstFrame_matrix]
  simp only [Matrix.updateCol_apply, augmentedVector, Pi.neg_apply, Pi.add_apply, Matrix.col,
    Matrix.transpose_apply]

theorem augmentedSecondFrame_entry (frame : NormalizedFrames) (row column : Fin 3) :
    (augmentedSecondFrame frame).val.val row column =
      if column = 1 then -(frame.val.val row 0 + frame.val.val row 1)
      else frame.val.val row column := by
  rw [augmentedSecondFrame_matrix]
  simp only [Matrix.updateCol_apply, augmentedVector, Pi.neg_apply, Pi.add_apply, Matrix.col,
    Matrix.transpose_apply]

def lastSwapFrame (frame : NormalizedFrames) : NormalizedFrames :=
  rightSwapFrame (rightCycleFrame (rightCycleFrame frame))

def outerSwapFrame (frame : NormalizedFrames) : NormalizedFrames :=
  rightSwapFrame (rightCycleFrame frame)

theorem frameSymbol_lastSwap (frame : NormalizedFrames) :
    frameSymbol (lastSwapFrame frame) = -frameSymbol frame := by
  rw [lastSwapFrame, frameSymbol_swap, frameSymbol_cycle, frameSymbol_cycle]

theorem frameSymbol_outerSwap (frame : NormalizedFrames) :
    frameSymbol (outerSwapFrame frame) = -frameSymbol frame := by
  rw [outerSwapFrame, frameSymbol_swap, frameSymbol_cycle]

def lastPairFirstFrame (frame : NormalizedFrames) : NormalizedFrames :=
  rightCycleFrame (rightCycleFrame (augmentedFirstFrame (rightCycleFrame frame)))

def lastPairSecondFrame (frame : NormalizedFrames) : NormalizedFrames :=
  rightCycleFrame (rightCycleFrame (augmentedSecondFrame (rightCycleFrame frame)))

def outerPairFirstFrame (frame : NormalizedFrames) : NormalizedFrames :=
  rightCycleFrame (augmentedSecondFrame (rightCycleFrame (rightCycleFrame frame)))

def outerPairSecondFrame (frame : NormalizedFrames) : NormalizedFrames :=
  rightCycleFrame (augmentedFirstFrame (rightCycleFrame (rightCycleFrame frame)))

theorem frameSymbol_lastPair (frame : NormalizedFrames) :
    frameSymbol frame = frameSymbol (lastPairFirstFrame frame) +
      frameSymbol (lastPairSecondFrame frame) := by
  simp only [lastPairFirstFrame, lastPairSecondFrame, frameSymbol_cycle]
  exact (frameSymbol_cycle frame).symm.trans (frameSymbol_augmented (rightCycleFrame frame))

theorem frameSymbol_outerPair (frame : NormalizedFrames) :
    frameSymbol frame = frameSymbol (outerPairFirstFrame frame) +
      frameSymbol (outerPairSecondFrame frame) := by
  simp only [outerPairFirstFrame, outerPairSecondFrame, frameSymbol_cycle]
  rw [add_comm]
  exact ((frameSymbol_cycle (rightCycleFrame frame)).trans (frameSymbol_cycle frame)).symm.trans
    (frameSymbol_augmented (rightCycleFrame (rightCycleFrame frame)))

theorem lastPairFirstFrame_entry (frame : NormalizedFrames) (row column : Fin 3) :
    (lastPairFirstFrame frame).val.val row column =
      if column = 1 then -(frame.val.val row 1 + frame.val.val row 2)
      else frame.val.val row column := by
  fin_cases column <;>
    simp [lastPairFirstFrame, rightCycleFrame_entry, augmentedFirstFrame_entry]

theorem lastPairSecondFrame_entry (frame : NormalizedFrames) (row column : Fin 3) :
    (lastPairSecondFrame frame).val.val row column =
      if column = 2 then -(frame.val.val row 1 + frame.val.val row 2)
      else frame.val.val row column := by
  fin_cases column <;>
    simp [lastPairSecondFrame, rightCycleFrame_entry, augmentedSecondFrame_entry]

theorem outerPairFirstFrame_entry (frame : NormalizedFrames) (row column : Fin 3) :
    (outerPairFirstFrame frame).val.val row column =
      if column = 0 then -(frame.val.val row 0 + frame.val.val row 2)
      else frame.val.val row column := by
  fin_cases column <;>
    simp [outerPairFirstFrame, rightCycleFrame_entry, augmentedSecondFrame_entry, add_comm]

theorem outerPairSecondFrame_entry (frame : NormalizedFrames) (row column : Fin 3) :
    (outerPairSecondFrame frame).val.val row column =
      if column = 2 then -(frame.val.val row 0 + frame.val.val row 2)
      else frame.val.val row column := by
  fin_cases column <;>
    simp [outerPairSecondFrame, rightCycleFrame_entry, augmentedFirstFrame_entry, add_comm]

def mixedFirstFrame (frame : NormalizedFrames) : NormalizedFrames :=
  outerPairFirstFrame (augmentedFirstFrame frame)

def mixedSecondFrame (frame : NormalizedFrames) : NormalizedFrames :=
  lastPairFirstFrame (augmentedSecondFrame frame)

def mixedThirdFrame (frame : NormalizedFrames) : NormalizedFrames :=
  augmentedFirstFrame (outerPairSecondFrame (augmentedFirstFrame frame))

def mixedVector (frame : NormalizedFrames) : Fin 3 → ℤ :=
  frame.val.val.col 0 + frame.val.val.col 1 - frame.val.val.col 2

theorem mixedFirstFrame_matrix (frame : NormalizedFrames) :
    (mixedFirstFrame frame).val.val = frame.val.val.updateCol 0 (mixedVector frame) := by
  ext row column
  fin_cases column <;>
    simp [mixedFirstFrame, outerPairFirstFrame_entry, augmentedFirstFrame_entry,
      Matrix.updateCol, mixedVector, Matrix.col]
  ring

theorem mixedSecondFrame_matrix (frame : NormalizedFrames) :
    (mixedSecondFrame frame).val.val = frame.val.val.updateCol 1 (mixedVector frame) := by
  ext row column
  fin_cases column <;>
    simp [mixedSecondFrame, lastPairFirstFrame_entry, augmentedSecondFrame_entry,
      Matrix.updateCol, mixedVector, Matrix.col]
  ring

theorem mixedThirdFrame_matrix (frame : NormalizedFrames) :
    (mixedThirdFrame frame).val.val = frame.val.val.updateCol 2 (mixedVector frame) := by
  ext row column
  fin_cases column <;>
    simp [mixedThirdFrame, augmentedFirstFrame_entry, outerPairSecondFrame_entry,
      Matrix.updateCol, mixedVector, Matrix.col]
  all_goals ring

theorem frameSymbol_mixed (frame : NormalizedFrames) :
    frameSymbol frame = frameSymbol (mixedFirstFrame frame) +
      frameSymbol (mixedSecondFrame frame) + frameSymbol (mixedThirdFrame frame) := by
  let first := augmentedFirstFrame frame
  let second := augmentedSecondFrame frame
  let residual := outerPairSecondFrame first
  have residualEquality : augmentedSecondFrame residual =
      rightSwapFrame (lastPairSecondFrame second) := by
    apply normalizedFrames_eq_of_matrix_eq
    ext row column
    fin_cases column <;>
      simp [residual, first, second, augmentedFirstFrame_entry, augmentedSecondFrame_entry,
        outerPairSecondFrame_entry, rightSwapFrame_entry, lastPairSecondFrame_entry,
        Equiv.swap_apply_def]
  have original := frameSymbol_augmented frame
  have firstRelation := frameSymbol_outerPair first
  have secondRelation := frameSymbol_lastPair second
  have residualRelation := frameSymbol_augmented residual
  rw [residualEquality, frameSymbol_swap] at residualRelation
  rw [← sub_eq_add_neg] at residualRelation
  change frameSymbol residual = frameSymbol (mixedThirdFrame frame) -
    frameSymbol (lastPairSecondFrame second) at residualRelation
  change frameSymbol first = frameSymbol (mixedFirstFrame frame) + frameSymbol residual at firstRelation
  change frameSymbol second = frameSymbol (mixedSecondFrame frame) +
    frameSymbol (lastPairSecondFrame second) at secondRelation
  change frameSymbol frame = frameSymbol first + frameSymbol second at original
  rw [original, firstRelation, secondRelation, residualRelation]
  abel

theorem mixedVector_normalized (frame : NormalizedFrames) :
    (mixedVector frame 2 : ZMod 3) = 1 := by
  change ((frame.val.val 2 0 + frame.val.val 2 1 - frame.val.val 2 2 : ℤ) : ZMod 3) = 1
  push_cast
  rw [frame.property 0, frame.property 1, frame.property 2]
  decide

def augmentedGoodLine (frame : NormalizedFrames) : GoodLines :=
  ⟨normalizedVectorLine (augmentedVector frame) (augmentedVector_normalized frame),
    normalizedVectorLine_good _ _⟩

def mixedGoodLine (frame : NormalizedFrames) : GoodLines :=
  ⟨normalizedVectorLine (mixedVector frame) (mixedVector_normalized frame),
    normalizedVectorLine_good _ _⟩

theorem normalizedFrameTriple_updateCol (original updated : NormalizedFrames)
    (vector : Fin 3 → ℤ) (normalized : (vector 2 : ZMod 3) = 1) (column : Fin 3)
    (equality : updated.val.val = original.val.val.updateCol column vector) :
    normalizedFrameTriple updated =
      ((if column = 0 then ⟨normalizedVectorLine vector normalized,
          normalizedVectorLine_good vector normalized⟩ else (normalizedFrameTriple original).1),
        (if column = 1 then ⟨normalizedVectorLine vector normalized,
          normalizedVectorLine_good vector normalized⟩ else (normalizedFrameTriple original).2.1),
        (if column = 2 then ⟨normalizedVectorLine vector normalized,
          normalizedVectorLine_good vector normalized⟩ else (normalizedFrameTriple original).2.2)) := by
  have columns (candidate : Fin 3) :
      columnLine (normalizedGoodRationalFrame updated).val candidate =
        if column = candidate then normalizedVectorLine vector normalized
          else columnLine (normalizedGoodRationalFrame original).val candidate := by
    apply flagSubspace_injective
    rw [columnLine_subspace]
    by_cases same : column = candidate
    · subst candidate
      rw [ite_eq_left rfl, normalizedVectorLine_subspace]
      have vectorEquality : (normalizedGoodRationalFrame updated).val.val.col column =
          integerVectorMap vector := by
        ext row
        change (updated.val.val row column : ℚ) = (vector row : ℚ)
        rw [equality]
        simp
      rw [vectorEquality]
    · rw [ite_eq_right same, columnLine_subspace]
      have vectorEquality : (normalizedGoodRationalFrame updated).val.val.col candidate =
          (normalizedGoodRationalFrame original).val.val.col candidate := by
        ext row
        change (updated.val.val row candidate : ℚ) = (original.val.val row candidate : ℚ)
        rw [equality]
        simp [Matrix.updateCol, Ne.symm same]
      rw [vectorEquality]
  fin_cases column
  all_goals
    apply Prod.ext
    · apply Subtype.ext
      simpa [normalizedFrameTriple, rationalFrameTriple] using columns 0
    · apply Prod.ext
      · apply Subtype.ext
        simpa [normalizedFrameTriple, rationalFrameTriple] using columns 1
      · apply Subtype.ext
        simpa [normalizedFrameTriple, rationalFrameTriple] using columns 2

theorem augmentedFirstFrame_triple (frame : NormalizedFrames) :
    normalizedFrameTriple (augmentedFirstFrame frame) =
      (augmentedGoodLine frame, (normalizedFrameTriple frame).2.1,
        (normalizedFrameTriple frame).2.2) := by
  simpa only [augmentedGoodLine, Fin.reduceEq, ↓reduceIte] using
    normalizedFrameTriple_updateCol frame (augmentedFirstFrame frame) (augmentedVector frame)
      (augmentedVector_normalized frame) 0 (augmentedFirstFrame_matrix frame)

theorem augmentedSecondFrame_triple (frame : NormalizedFrames) :
    normalizedFrameTriple (augmentedSecondFrame frame) =
      ((normalizedFrameTriple frame).1, augmentedGoodLine frame,
        (normalizedFrameTriple frame).2.2) := by
  simpa only [augmentedGoodLine, Fin.reduceEq, ↓reduceIte] using
    normalizedFrameTriple_updateCol frame (augmentedSecondFrame frame) (augmentedVector frame)
      (augmentedVector_normalized frame) 1 (augmentedSecondFrame_matrix frame)

theorem mixedFirstFrame_triple (frame : NormalizedFrames) :
    normalizedFrameTriple (mixedFirstFrame frame) =
      (mixedGoodLine frame, (normalizedFrameTriple frame).2.1,
        (normalizedFrameTriple frame).2.2) := by
  simpa only [mixedGoodLine, Fin.reduceEq, ↓reduceIte] using
    normalizedFrameTriple_updateCol frame (mixedFirstFrame frame) (mixedVector frame)
      (mixedVector_normalized frame) 0 (mixedFirstFrame_matrix frame)

theorem mixedSecondFrame_triple (frame : NormalizedFrames) :
    normalizedFrameTriple (mixedSecondFrame frame) =
      ((normalizedFrameTriple frame).1, mixedGoodLine frame,
        (normalizedFrameTriple frame).2.2) := by
  simpa only [mixedGoodLine, Fin.reduceEq, ↓reduceIte] using
    normalizedFrameTriple_updateCol frame (mixedSecondFrame frame) (mixedVector frame)
      (mixedVector_normalized frame) 1 (mixedSecondFrame_matrix frame)

theorem mixedThirdFrame_triple (frame : NormalizedFrames) :
    normalizedFrameTriple (mixedThirdFrame frame) =
      ((normalizedFrameTriple frame).1, (normalizedFrameTriple frame).2.1,
        mixedGoodLine frame) := by
  simpa only [mixedGoodLine, Fin.reduceEq, ↓reduceIte] using
    normalizedFrameTriple_updateCol frame (mixedThirdFrame frame) (mixedVector frame)
      (mixedVector_normalized frame) 2 (mixedThirdFrame_matrix frame)

theorem rationalSymbol_mixed (frame : NormalizedFrames) :
    symbol (normalizedFrameTriple frame).1 (normalizedFrameTriple frame).2.1
        (normalizedFrameTriple frame).2.2 =
      symbol (mixedGoodLine frame) (normalizedFrameTriple frame).2.1
        (normalizedFrameTriple frame).2.2 +
      symbol (normalizedFrameTriple frame).1 (mixedGoodLine frame)
        (normalizedFrameTriple frame).2.2 +
      symbol (normalizedFrameTriple frame).1 (normalizedFrameTriple frame).2.1
        (mixedGoodLine frame) := by
  have equality := congrArg integralToRationalSymbols (frameSymbol_mixed frame)
  simpa only [map_add, integralToRationalSymbols_frameSymbol, mixedFirstFrame_triple,
    mixedSecondFrame_triple, mixedThirdFrame_triple] using equality

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.FrameMoves
