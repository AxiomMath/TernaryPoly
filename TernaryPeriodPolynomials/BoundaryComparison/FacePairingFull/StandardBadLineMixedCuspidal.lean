module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.MixedSubgroup
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.BadLineEdges
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.SubgroupVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InnerMixed
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalReconstruction

@[expose] public section


/-!
# Locally inner classes at the standard bad line are the mixed cuspidal classes

At the standard bad line `F₀` (stabilizer `N ⋊ L` with `N ≅ ℤ²` the radical and
`L = ℤˣ × binaryArithmeticLevel` the arithmetic Levi), the paper's mixed cuspidal condition
on a class `c ∈ H²(Γ_{F₀}, E)` has two parts (end of Appendix C.4, Hochschild–Serre):

* `c` has zero restriction to the radical `N`, so that it lies in the `(1,1)` term, i.e. it has a
  well-defined mixed class `m(c) ∈ H¹(L, H¹(N, E))`;
* `m(c)` has zero restriction to the cusp subgroup `ℤˣ × (binary cusp stabilizer)` of every
  rational cusp (frame) of the binary Levi.

`locallyInner_iff_mixedCuspidal` proves that this is equivalent to the library's condition that
`c` restricts to zero on the stabilizer of every complete flag over `F₀`
(`locallyInnerClasses`), the local form of `InnerBoundary`
(`innerBoundary_iff_locallyInner`). The forward direction is the library's
`locallyInner_mixed_restriction_zero`; the converse combines the Hochschild–Serre exactness of
`MixedSubgroup` for the subgroup `N ⋊ (ℤˣ × cusp)` (the edge stabilizer, `BadLineEdges`) with the
inhomogeneous-to-homogeneous primitive transfer of `SubgroupVanishing`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

/-- The cusp subgroup of the arithmetic Levi `ℤˣ × GL₂` at the rational cusp of `frame`. -/
def leviCusp (frame : GeneralLinearGroup (Fin 2) ℚ) : Subgroup (ℤˣ × binaryArithmeticLevel) :=
  (⊤ : Subgroup ℤˣ).prod (binaryCuspLevel frame)

/-- **Mixed cuspidal at the standard bad line.** The class has zero restriction to the radical
and its mixed class in `H¹(L, H¹(N, E))` has zero restriction to the cusp subgroup of every
rational cusp of the binary Levi. -/
def MixedCuspidal (degree : ℕ)
    (coordinate : H2 (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter)) : Prop :=
  ∃ radicalZero : standardBadLineInhomogeneousH2Equiv degree coordinate ∈
      (radicalRestrictionH2 integralBadLineSplitting.conjAct
        (standardBadLineRepresentation degree)).ker,
    ∀ frame : GeneralLinearGroup (Fin 2) ℚ,
      crossedPullbackH1 (leviCusp frame).subtype
        (leviCrossedH1Representation integralBadLineSplitting.conjAct
          (standardBadLineRepresentation degree))
        (radicalKernelMixedMap integralBadLineSplitting.conjAct
          (standardBadLineRepresentation degree) ⟨_, radicalZero⟩) = 0

/-- An element of the standard bad-line stabilizer fixes `binaryEdge frame` exactly when the
binary part of its Levi component lies in the cusp subgroup of `frame`. -/
theorem mem_edgeSubgroup_iff (frame : GeneralLinearGroup (Fin 2) ℚ) (x : BadLineSemidirect) :
    x ∈ standardBadLineEdgeSubgroup (binaryEdge frame) ↔ x.right.2 ∈ binaryCuspLevel frame := by
  have fact : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right := by
    apply SemidirectProduct.ext <;> simp
  have hl : standardBadLineAmbientHom (SemidirectProduct.inl x.left) ∈
      fixedPointLevel rationalLevel (binaryEdge frame) := binaryEdge_radical_mem frame x.left
  have split : standardBadLineAmbientHom x = standardBadLineAmbientHom
      (SemidirectProduct.inl x.left) * standardBadLineAmbientHom
        (SemidirectProduct.inr x.right) := by
    conv_lhs => rw [fact]
    rw [map_mul]
  change standardBadLineAmbientHom x ∈ fixedPointLevel rationalLevel (binaryEdge frame) ↔ _
  rw [split]
  constructor
  · intro h
    have h2 := (Subgroup.mul_mem_cancel_left _ hl).mp h
    exact (ambient_inr_mem_edge_iff frame x.right.1 x.right.2).mp h2
  · intro h
    exact Subgroup.mul_mem _ hl ((ambient_inr_mem_edge_iff frame x.right.1 x.right.2).mpr h)

/-- Locally inner classes are mixed cuspidal. -/
theorem MixedCuspidal.of_locallyInner (degree : ℕ)
    (coordinate : H2 (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter))
    (inner : coordinate ∈ locallyInnerClasses degree trivialCharacter .line standardBadLine) :
    MixedCuspidal degree coordinate := by
  have radicalZero := locallyInner_standardBadLine_radical_zero degree coordinate inner
  refine ⟨radicalZero, fun frame => ?_⟩
  exact locallyInner_mixed_restriction_zero degree (binaryEdge frame) (binaryEdge_endpoint frame)
    (leviCusp frame).subtype (fun radical => binaryEdge_radical_mem frame radical)
    (fun element => (mem_edgeSubgroup_iff frame _).mpr (Subgroup.mem_prod.mp element.property).2)
    ⟨coordinate, inner⟩

/-- Mixed cuspidal classes are locally inner: **the converse**. -/
theorem locallyInner_of_mixedCuspidal (degree : ℕ)
    (coordinate : H2 (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter))
    (mixed : MixedCuspidal degree coordinate) :
    coordinate ∈ locallyInnerClasses degree trivialCharacter .line standardBadLine := by
  obtain ⟨radicalZero, cuspZero⟩ := mixed
  apply (Submodule.mem_iInf
    (M := H2 (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter)) _).mpr
  rintro ⟨edge, endpointEq⟩
  have edgeExists := exists_binaryEdge edge endpointEq
  obtain ⟨frame, rfl⟩ := edgeExists
  have originalExists := (LinearMap.range (boundaryMap (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter))).mkQ_surjective coordinate
  obtain ⟨original, originalClass⟩ := originalExists
  have representative := radicalRestrictionH2_ker_representative
    integralBadLineSplitting.conjAct (standardBadLineRepresentation degree)
    (standardBadLineInhomogeneousH2Equiv degree coordinate) radicalZero
  obtain ⟨cycle, cycleClass⟩ := representative
  have mixedEq : radicalKernelMixedMap integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree)
        ⟨standardBadLineInhomogeneousH2Equiv degree coordinate, radicalZero⟩ =
      mixedClassMap integralBadLineSplitting.conjAct (standardBadLineRepresentation degree)
        cycle := by
    have same : (⟨standardBadLineInhomogeneousH2Equiv degree coordinate, radicalZero⟩ :
        (radicalRestrictionH2 integralBadLineSplitting.conjAct
          (standardBadLineRepresentation degree)).ker) =
        radicalZeroH2ToKernel integralBadLineSplitting.conjAct
          (standardBadLineRepresentation degree)
          ((radicalZeroBoundaries integralBadLineSplitting.conjAct
            (standardBadLineRepresentation degree)).mkQ cycle) :=
      Subtype.ext cycleClass.symm
    have step := radicalKernelMixedMap_representative integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree) cycle
    have unfoldRight : mixedClassMap integralBadLineSplitting.conjAct
        (standardBadLineRepresentation degree) cycle =
        (crossedBoundaries (leviCrossedH1Representation integralBadLineSplitting.conjAct
          (standardBadLineRepresentation degree))).mkQ
          (mixedH1CocycleMap integralBadLineSplitting.conjAct
            (standardBadLineRepresentation degree) cycle) :=
      LinearMap.comp_apply _ _ _
    exact (congrArg (radicalKernelMixedMap integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree)) same).trans (step.trans unfoldRight.symm)
  have zero : crossedPullbackH1 (leviCusp frame).subtype
      (leviCrossedH1Representation integralBadLineSplitting.conjAct
        (standardBadLineRepresentation degree))
      (mixedClassMap integralBadLineSplitting.conjAct (standardBadLineRepresentation degree)
        cycle) = 0 := by
    exact (congrArg (crossedPullbackH1 (leviCusp frame).subtype
      (leviCrossedH1Representation integralBadLineSplitting.conjAct
        (standardBadLineRepresentation degree))) mixedEq).symm.trans (cuspZero frame)
  let central : leviCusp frame := ⟨badLineLeviReflection,
    Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, (binaryCuspLevel frame).one_mem⟩⟩
  have primitiveExists := exists_primitive_of_pullback_mixed_zero
    integralBadLineSplitting.conjAct (standardBadLineRepresentation degree) (leviCusp frame)
    central (fun b => Subtype.ext (badLineLeviReflection_central b.val))
    (fun v hv => congrArg Subtype.val (standardBadLineInvariant_reflection degree ⟨v, hv⟩))
    cycle zero
  obtain ⟨primitive, primitiveBoundary⟩ := primitiveExists
  have sameClass : (inhomogeneousBoundaries (standardBadLineRepresentation degree)).mkQ cycle.val =
      (inhomogeneousBoundaries (standardBadLineRepresentation degree)).mkQ
        (standardBadLineSemidirectCycle degree original) := by
    rw [cycleClass, ← standardBadLineInhomogeneousH2Equiv_classOf]
    exact congrArg _ originalClass.symm
  have correctionExists :=
    (Submodule.Quotient.eq (inhomogeneousBoundaries (standardBadLineRepresentation degree))).mp
      sameClass
  obtain ⟨correction, correctionBoundary⟩ := correctionExists
  rw [LinearMap.mem_ker]
  have hle := fixedPointLevel_edge_le_flag .line (binaryEdge frame) standardBadLine endpointEq
  rw [← originalClass]
  refine subgroupRestrictionH2_classOf_eq_zero hle _ original
    (fun a => (primitive - correction)
      (standardBadLineSemidirectEquiv.symm ⟨a.val, hle a.property⟩)) ?_
  intro a b
  let X : BadLineSemidirect := standardBadLineSemidirectEquiv.symm ⟨a.val, hle a.property⟩
  let Y : BadLineSemidirect := standardBadLineSemidirectEquiv.symm ⟨b.val, hle b.property⟩
  have hX : (standardBadLineSemidirectEquiv X).val = a.val := by
    simp only [X, MulEquiv.apply_symm_apply]
  have hY : (standardBadLineSemidirectEquiv Y).val = b.val := by
    simp only [Y, MulEquiv.apply_symm_apply]
  have hXY : X * Y = standardBadLineSemidirectEquiv.symm ⟨(a * b).val, hle (a * b).property⟩ := by
    simp only [X, Y]
    rw [← map_mul]
    rfl
  have memX : X ∈ standardBadLineEdgeSubgroup (binaryEdge frame) := by
    change (standardBadLineSemidirectEquiv X).val ∈ fixedPointLevel rationalLevel (binaryEdge frame)
    rw [hX]
    exact a.property
  have memY : Y ∈ standardBadLineEdgeSubgroup (binaryEdge frame) := by
    change (standardBadLineSemidirectEquiv Y).val ∈ fixedPointLevel rationalLevel (binaryEdge frame)
    rw [hY]
    exact b.property
  have rightX : X.right ∈ leviCusp frame :=
    Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, (mem_edgeSubgroup_iff frame X).mp memX⟩
  have rightY : Y.right ∈ leviCusp frame :=
    Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, (mem_edgeSubgroup_iff frame Y).mp memY⟩
  have hB := primitiveBoundary X Y rightX rightY
  have hC := congrArg (fun f => f.val X Y) correctionBoundary
  have key : (inhomogeneousBoundaryMap (standardBadLineRepresentation degree)
      (primitive - correction)).val X Y =
      (standardBadLineSemidirectCycle degree original).val X Y := by
    have hC' : (inhomogeneousBoundaryMap (standardBadLineRepresentation degree)
        correction).val X Y = cycle.val.val X Y -
          (standardBadLineSemidirectCycle degree original).val X Y := hC
    rw [map_sub]
    change (inhomogeneousBoundaryMap (standardBadLineRepresentation degree) primitive).val X Y -
      (inhomogeneousBoundaryMap (standardBadLineRepresentation degree) correction).val X Y = _
    rw [hB, hC']
    abel
  rw [standardBadLineSemidirectCycle_apply, hX, hY] at key
  have hρ : standardBadLineRepresentation degree X =
      rationalCoefficientComponent degree trivialCharacter a.val := by
    change rationalCoefficientComponent degree trivialCharacter
      (standardBadLineSemidirectEquiv X).val = _
    rw [hX]
  have key' : standardBadLineRepresentation degree X ((primitive - correction) Y) -
      (primitive - correction) (X * Y) + (primitive - correction) X =
      original.val.val ![1, a.val, a.val * b.val] := key
  rw [hρ, hXY] at key'
  exact key'

end TernaryPeriodPolynomials.Argument.FacePairingFull
