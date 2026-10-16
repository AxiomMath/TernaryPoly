module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LeviVanishing

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

def standardBadLineInnerToRadicalKernel (degree : ℕ) :
    locallyInnerClasses degree trivialCharacter .line standardBadLine →ₗ[ℂ]
      (radicalRestrictionH2 integralBadLineSplitting.conjAct
        (standardBadLineRepresentation degree)).ker :=
  ((standardBadLineInhomogeneousH2Equiv degree).toLinearMap.comp
    (locallyInnerClasses degree trivialCharacter .line standardBadLine).subtype).codRestrict _
    (fun coordinate => locallyInner_standardBadLine_radical_zero degree
      coordinate.val coordinate.property)

theorem standardBadLineInnerToRadicalKernel_injective (degree : ℕ) :
    Function.Injective (standardBadLineInnerToRadicalKernel degree) := by
  intro first second equality
  apply Subtype.ext
  apply (standardBadLineInhomogeneousH2Equiv degree).injective
  exact congrArg Subtype.val equality

def standardBadLineInnerMixedMap (degree : ℕ) :
    locallyInnerClasses degree trivialCharacter .line standardBadLine →ₗ[ℂ]
      CrossedH1 (leviCrossedH1Representation integralBadLineSplitting.conjAct
        (standardBadLineRepresentation degree)) :=
  (radicalKernelMixedMap integralBadLineSplitting.conjAct
    (standardBadLineRepresentation degree)).comp
      (standardBadLineInnerToRadicalKernel degree)

theorem standardBadLineInnerMixedMap_injective (degree : ℕ) :
    Function.Injective (standardBadLineInnerMixedMap degree) :=
  (standardBadLineMixedMap_injective degree).comp
    (standardBadLineInnerToRadicalKernel_injective degree)

theorem standardBadLineInnerMixedMap_zero_iff (degree : ℕ)
    (coordinate : locallyInnerClasses degree trivialCharacter .line standardBadLine) :
    standardBadLineInnerMixedMap degree coordinate = 0 ↔ coordinate = 0 := by
  constructor
  · intro zero
    apply standardBadLineInnerMixedMap_injective degree
    exact zero.trans (map_zero _).symm
  · rintro rfl
    exact map_zero _

theorem standardBadLineInnerMixedMap_representative (degree : ℕ)
    (coordinate : locallyInnerClasses degree trivialCharacter .line standardBadLine)
    (cycle : radicalZeroTwoCycles integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree))
    (represents : (inhomogeneousBoundaries (standardBadLineRepresentation degree)).mkQ cycle.val =
      standardBadLineInhomogeneousH2Equiv degree coordinate.val) :
    standardBadLineInnerMixedMap degree coordinate =
      mixedClassMap integralBadLineSplitting.conjAct (standardBadLineRepresentation degree) cycle := by
  have equality : standardBadLineInnerToRadicalKernel degree coordinate =
      radicalZeroH2ToKernel integralBadLineSplitting.conjAct (standardBadLineRepresentation degree)
        ((radicalZeroBoundaries integralBadLineSplitting.conjAct
          (standardBadLineRepresentation degree)).mkQ cycle) := Subtype.ext represents.symm
  have step := radicalKernelMixedMap_representative integralBadLineSplitting.conjAct
    (standardBadLineRepresentation degree) cycle
  have unfoldLeft : standardBadLineInnerMixedMap degree coordinate =
      radicalKernelMixedMap integralBadLineSplitting.conjAct
        (standardBadLineRepresentation degree)
        (standardBadLineInnerToRadicalKernel degree coordinate) :=
    LinearMap.comp_apply _ _ _
  have unfoldRight : mixedClassMap integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree) cycle =
      (crossedBoundaries (leviCrossedH1Representation integralBadLineSplitting.conjAct
        (standardBadLineRepresentation degree))).mkQ
        (mixedH1CocycleMap integralBadLineSplitting.conjAct
          (standardBadLineRepresentation degree) cycle) :=
    LinearMap.comp_apply _ _ _
  exact unfoldLeft.trans ((congrArg (radicalKernelMixedMap integralBadLineSplitting.conjAct
    (standardBadLineRepresentation degree)) equality).trans (step.trans unfoldRight.symm))

def innerBadLineMixedMap (degree : ℕ) :
    innerBadLineClasses degree →ₗ[ℂ]
      CrossedH1 (leviCrossedH1Representation integralBadLineSplitting.conjAct
        (standardBadLineRepresentation degree)) :=
  (standardBadLineInnerMixedMap degree).comp (innerBadLineLocalEquiv degree).toLinearMap

theorem innerBadLineMixedMap_injective (degree : ℕ) :
    Function.Injective (innerBadLineMixedMap degree) :=
  (standardBadLineInnerMixedMap_injective degree).comp (innerBadLineLocalEquiv degree).injective

theorem innerBadLineMixedMap_zero_iff (degree : ℕ) (coordinate : innerBadLineClasses degree) :
    innerBadLineMixedMap degree coordinate = 0 ↔ coordinate = 0 := by
  constructor
  · intro zero
    apply innerBadLineMixedMap_injective degree
    exact zero.trans (map_zero _).symm
  · rintro rfl
    exact map_zero _

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
