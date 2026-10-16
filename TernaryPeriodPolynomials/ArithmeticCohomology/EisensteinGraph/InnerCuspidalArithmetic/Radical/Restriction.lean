module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Mixed.Descent
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.GroupEquivCohomology

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

section Pullback

variable {Source Target Value : Type} [Group Source] [Group Target]
  [AddCommGroup Value] [Module ℂ Value]
  (homomorphism : Source →* Target) (representation : Representation ℂ Target Value)

def inhomogeneousPullbackCycles :
    inhomogeneousTwoCycles representation →ₗ[ℂ]
      inhomogeneousTwoCycles (representation.comp homomorphism) where
  toFun cycle := ⟨fun first second => cycle.val (homomorphism first) (homomorphism second), by
    intro first second third
    simpa only [MonoidHom.comp_apply, map_mul] using
      cycle.property (homomorphism first) (homomorphism second) (homomorphism third)⟩
  map_add' first second := rfl
  map_smul' scalar cycle := rfl

theorem inhomogeneousPullbackCycles_boundary (cochain : Target → Value) :
    inhomogeneousPullbackCycles homomorphism representation
        (inhomogeneousBoundaryMap representation cochain) =
      inhomogeneousBoundaryMap (representation.comp homomorphism)
        (cochain ∘ homomorphism) := by
  apply Subtype.ext
  funext first second
  change representation (homomorphism first) (cochain (homomorphism second)) -
        cochain (homomorphism first * homomorphism second) + cochain (homomorphism first) =
      representation (homomorphism first) (cochain (homomorphism second)) -
        cochain (homomorphism (first * second)) + cochain (homomorphism first)
  rw [map_mul]

theorem inhomogeneousPullbackCycles_boundaries :
    inhomogeneousBoundaries representation ≤
      (inhomogeneousBoundaries (representation.comp homomorphism)).comap
        (inhomogeneousPullbackCycles homomorphism representation) := by
  rintro cycle ⟨cochain, rfl⟩
  exact ⟨cochain ∘ homomorphism,
    (inhomogeneousPullbackCycles_boundary homomorphism representation cochain).symm⟩

def inhomogeneousPullbackH2 :
    InhomogeneousH2 representation →ₗ[ℂ]
      InhomogeneousH2 (representation.comp homomorphism) :=
  (inhomogeneousBoundaries representation).mapQ
    (inhomogeneousBoundaries (representation.comp homomorphism))
    (inhomogeneousPullbackCycles homomorphism representation)
    (inhomogeneousPullbackCycles_boundaries homomorphism representation)

theorem inhomogeneousPullbackH2_mk (cycle : inhomogeneousTwoCycles representation) :
    inhomogeneousPullbackH2 homomorphism representation
        ((inhomogeneousBoundaries representation).mkQ cycle) =
      (inhomogeneousBoundaries (representation.comp homomorphism)).mkQ
        (inhomogeneousPullbackCycles homomorphism representation cycle) := by
  rfl

end Pullback

section Radical

variable {Radical Levi Value : Type} [Group Radical] [Group Levi]
  [AddCommGroup Value] [Module ℂ Value]
  (action : Levi →* MulAut Radical)
  (representation : Representation ℂ (SemidirectProduct Radical Levi action) Value)

def radicalRestrictionH2 :
    InhomogeneousH2 representation →ₗ[ℂ]
      InhomogeneousH2 (representation.comp SemidirectProduct.inl) :=
  inhomogeneousPullbackH2 SemidirectProduct.inl representation

theorem radicalZeroH2ToFull_mem_ker (coordinate : RadicalZeroH2 action representation) :
    radicalZeroH2ToFull action representation coordinate ∈
      (radicalRestrictionH2 action representation).ker := by
  obtain ⟨cycle, rfl⟩ := (radicalZeroBoundaries action representation).mkQ_surjective coordinate
  change (inhomogeneousBoundaries (representation.comp SemidirectProduct.inl)).mkQ
      (inhomogeneousPullbackCycles SemidirectProduct.inl representation cycle.val) = 0
  have zero : inhomogeneousPullbackCycles SemidirectProduct.inl representation cycle.val = 0 := by
    apply Subtype.ext
    funext first second
    exact cycle.property first second
  rw [zero, map_zero]

theorem radicalRestrictionH2_ker_representative
    (coordinate : InhomogeneousH2 representation)
    (zero : coordinate ∈ (radicalRestrictionH2 action representation).ker) :
    ∃ cycle : radicalZeroTwoCycles action representation,
      (inhomogeneousBoundaries representation).mkQ cycle.val = coordinate := by
  obtain ⟨original, rfl⟩ := (inhomogeneousBoundaries representation).mkQ_surjective coordinate
  change (inhomogeneousBoundaries (representation.comp SemidirectProduct.inl)).mkQ
      (inhomogeneousPullbackCycles SemidirectProduct.inl representation original) = 0 at zero
  obtain ⟨primitive, restriction⟩ :=
    (Submodule.Quotient.mk_eq_zero
      (inhomogeneousBoundaries (representation.comp SemidirectProduct.inl))).mp zero
  let extension : SemidirectProduct Radical Levi action → Value :=
    fun element => primitive element.left
  let corrected := original - inhomogeneousBoundaryMap representation extension
  have correctedZero : corrected ∈ radicalZeroTwoCycles action representation := by
    intro first second
    have pointwise := congrArg
      (fun cycle : inhomogeneousTwoCycles (representation.comp SemidirectProduct.inl) =>
        cycle.val first second) restriction
    change representation (SemidirectProduct.inl first) (primitive second) -
      primitive (first * second) + primitive first =
        original.val (SemidirectProduct.inl first) (SemidirectProduct.inl second) at pointwise
    change original.val (SemidirectProduct.inl first) (SemidirectProduct.inl second) -
      (representation (SemidirectProduct.inl first)
          (extension (SemidirectProduct.inl second)) -
        extension (SemidirectProduct.inl first * SemidirectProduct.inl second) +
        extension (SemidirectProduct.inl first)) = 0
    rw [← map_mul]
    exact sub_eq_zero.mpr pointwise.symm
  refine ⟨⟨corrected, correctedZero⟩, ?_⟩
  change (inhomogeneousBoundaries representation).mkQ
      (original - inhomogeneousBoundaryMap representation extension) =
    (inhomogeneousBoundaries representation).mkQ original
  rw [map_sub]
  have boundaryZero : (inhomogeneousBoundaries representation).mkQ
      (inhomogeneousBoundaryMap representation extension) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨extension, rfl⟩
  rw [boundaryZero, sub_zero]

def radicalZeroH2ToKernel :
    RadicalZeroH2 action representation →ₗ[ℂ]
      (radicalRestrictionH2 action representation).ker :=
  (radicalZeroH2ToFull action representation).codRestrict _
    (radicalZeroH2ToFull_mem_ker action representation)

theorem radicalZeroH2ToKernel_bijective :
    Function.Bijective (radicalZeroH2ToKernel action representation) := by
  constructor
  · intro first second equality
    apply radicalZeroH2ToFull_injective action representation
    exact congrArg Subtype.val equality
  · intro coordinate
    obtain ⟨cycle, equality⟩ := radicalRestrictionH2_ker_representative action representation
      coordinate.val coordinate.property
    refine ⟨(radicalZeroBoundaries action representation).mkQ cycle, ?_⟩
    apply Subtype.ext
    exact equality

def radicalRestrictionKernelEquiv :
    RadicalZeroH2 action representation ≃ₗ[ℂ]
      (radicalRestrictionH2 action representation).ker :=
  LinearEquiv.ofBijective (radicalZeroH2ToKernel action representation)
    (radicalZeroH2ToKernel_bijective action representation)

def radicalKernelMixedMap :
    (radicalRestrictionH2 action representation).ker →ₗ[ℂ]
      CrossedH1 (leviCrossedH1Representation action representation) :=
  (mixedH2Descent action representation).comp
    (radicalRestrictionKernelEquiv action representation).symm.toLinearMap

theorem radicalKernelMixedMap_representative
    (cycle : radicalZeroTwoCycles action representation) :
    radicalKernelMixedMap action representation
        (radicalZeroH2ToKernel action representation
          ((radicalZeroBoundaries action representation).mkQ cycle)) =
      (crossedBoundaries (leviCrossedH1Representation action representation)).mkQ
        (mixedH1CocycleMap action representation cycle) := by
  change mixedH2Descent action representation
      ((radicalRestrictionKernelEquiv action representation).symm
        ((radicalRestrictionKernelEquiv action representation)
          ((radicalZeroBoundaries action representation).mkQ cycle))) = _
  rw [LinearEquiv.symm_apply_apply, mixedH2Descent_mk]

def standardBadLineInhomogeneousH2Equiv (degree : ℕ) :
    H2 (fixedPointLevel rationalLevel standardBadLine)
        (rationalCoefficientComponent degree trivialCharacter) ≃ₗ[ℂ]
      InhomogeneousH2
        ((((rationalCoefficientComponent degree trivialCharacter).comp
          (fixedPointLevel rationalLevel standardBadLine).subtype).comp
            standardBadLineSemidirectEquiv.toMonoidHom)) :=
  (standardBadLineH2SemidirectEquiv degree).trans (fullInhomogeneousH2Equiv _)

end Radical

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
