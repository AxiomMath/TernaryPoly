module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Mixed.Restriction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

def standardBadLineAmbientHom : BadLineSemidirect →* RationalGL3 :=
  (fixedPointLevel rationalLevel standardBadLine).subtype.comp
    standardBadLineSemidirectEquiv.toMonoidHom

def standardBadLineEdgeSubgroup (edge : Edges) : Subgroup BadLineSemidirect :=
  (fixedPointLevel rationalLevel edge).comap standardBadLineAmbientHom

def standardBadLineCochainPrimitive (degree : ℕ) (edge : Edges)
    (primitive : cochains (fixedPointLevel rationalLevel edge)
      (rationalCoefficientComponent degree trivialCharacter) 1) :
    BadLineSemidirect → HomogeneousPoly degree :=
  fun element => primitive.val ![1, standardBadLineAmbientHom element]

theorem standardBadLineCochainPrimitive_boundary (degree : ℕ) (edge : Edges)
    (primitive : cochains (fixedPointLevel rationalLevel edge)
      (rationalCoefficientComponent degree trivialCharacter) 1)
    (first second : BadLineSemidirect) (firstMem : first ∈ standardBadLineEdgeSubgroup edge) :
    (inhomogeneousBoundaryMap (standardBadLineRepresentation degree)
      (standardBadLineCochainPrimitive degree edge primitive)).val first second =
      (boundaryMap (fixedPointLevel rationalLevel edge)
        (rationalCoefficientComponent degree trivialCharacter) primitive).val.val
        ![1, standardBadLineAmbientHom first,
          standardBadLineAmbientHom first * standardBadLineAmbientHom second] := by
  have equivariance := primitive.property ⟨standardBadLineAmbientHom first, firstMem⟩
    ![1, standardBadLineAmbientHom second]
  rw [ambientMapVectorTwo, mul_one] at equivariance
  change rationalCoefficientComponent degree trivialCharacter (standardBadLineAmbientHom first)
      (primitive.val ![1, standardBadLineAmbientHom second]) -
    primitive.val ![1, standardBadLineAmbientHom (first * second)] +
    primitive.val ![1, standardBadLineAmbientHom first] =
      primitive.val ![standardBadLineAmbientHom first,
        standardBadLineAmbientHom first * standardBadLineAmbientHom second] -
      primitive.val ![1, standardBadLineAmbientHom first * standardBadLineAmbientHom second] +
      primitive.val ![1, standardBadLineAmbientHom first]
  rw [equivariance, map_mul]

theorem locallyInner_cycle_boundary_on_edge (degree : ℕ) (edge : Edges)
    (endpointEq : endpoint .line edge = standardBadLine)
    (coordinate : locallyInnerClasses degree trivialCharacter .line standardBadLine)
    (cycle : inhomogeneousTwoCycles (standardBadLineRepresentation degree))
    (represents : (inhomogeneousBoundaries (standardBadLineRepresentation degree)).mkQ cycle =
      standardBadLineInhomogeneousH2Equiv degree coordinate.val) :
    ∃ primitive : BadLineSemidirect → HomogeneousPoly degree,
      ∀ first ∈ standardBadLineEdgeSubgroup edge, ∀ second ∈ standardBadLineEdgeSubgroup edge,
        (inhomogeneousBoundaryMap (standardBadLineRepresentation degree) primitive).val first second =
          cycle.val first second := by
  obtain ⟨original, originalClass⟩ :=
    (LinearMap.range (boundaryMap (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter))).mkQ_surjective coordinate.val
  have innerOriginal : classOf (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter) original ∈
      locallyInnerClasses degree trivialCharacter .line standardBadLine :=
    originalClass.symm ▸ coordinate.property
  have edgeZero := (Submodule.mem_iInf
    (M := H2 (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter)) _).mp innerOriginal ⟨edge, endpointEq⟩
  change classOf (fixedPointLevel rationalLevel edge)
    (rationalCoefficientComponent degree trivialCharacter)
    (subgroupRestrictionCycle
      (fixedPointLevel_edge_le_flag .line edge standardBadLine endpointEq)
      (rationalCoefficientComponent degree trivialCharacter) original) = 0 at edgeZero
  obtain ⟨edgePrimitive, edgeBoundary⟩ := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range (boundaryMap (fixedPointLevel rationalLevel edge)
      (rationalCoefficientComponent degree trivialCharacter)))).mp edgeZero
  have baseRepresents := standardBadLineInhomogeneousH2Equiv_classOf degree original
  change standardBadLineInhomogeneousH2Equiv degree
    ((LinearMap.range (boundaryMap (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter))).mkQ original) = _ at baseRepresents
  rw [originalClass] at baseRepresents
  have sameClass := represents.trans baseRepresents
  obtain ⟨correction, correctionBoundary⟩ := (Submodule.Quotient.eq
    (inhomogeneousBoundaries (standardBadLineRepresentation degree))).mp sameClass
  let base := standardBadLineCochainPrimitive degree edge edgePrimitive
  have baseBoundary : ∀ first ∈ standardBadLineEdgeSubgroup edge, ∀ second,
      (inhomogeneousBoundaryMap (standardBadLineRepresentation degree) base).val first second =
        (standardBadLineSemidirectCycle degree original).val first second := by
    intro first firstMem second
    rw [standardBadLineCochainPrimitive_boundary degree edge edgePrimitive first second firstMem,
      edgeBoundary, standardBadLineSemidirectCycle_apply]
    rfl
  refine ⟨base + correction, ?_⟩
  intro first firstMem second _secondMem
  rw [map_add]
  change (inhomogeneousBoundaryMap (standardBadLineRepresentation degree) base).val first second +
    (inhomogeneousBoundaryMap (standardBadLineRepresentation degree) correction).val first second = _
  rw [baseBoundary first firstMem second, correctionBoundary]
  change (standardBadLineSemidirectCycle degree original).val first second +
    (cycle.val first second - (standardBadLineSemidirectCycle degree original).val first second) = _
  rw [← add_sub_assoc, add_sub_cancel_left]

theorem locallyInner_mixed_restriction_zero {Smaller : Type} [Group Smaller]
    (degree : ℕ) (edge : Edges) (endpointEq : endpoint .line edge = standardBadLine)
    (homomorphism : Smaller →* (ℤˣ × binaryArithmeticLevel))
    (radicalMem : ∀ radical, SemidirectProduct.inl radical ∈ standardBadLineEdgeSubgroup edge)
    (leviMem : ∀ element, SemidirectProduct.inr (homomorphism element) ∈
      standardBadLineEdgeSubgroup edge)
    (coordinate : locallyInnerClasses degree trivialCharacter .line standardBadLine) :
    crossedPullbackH1 homomorphism
      (leviCrossedH1Representation integralBadLineSplitting.conjAct (standardBadLineRepresentation degree))
      (standardBadLineInnerMixedMap degree coordinate) = 0 := by
  have representative := radicalRestrictionH2_ker_representative
    integralBadLineSplitting.conjAct (standardBadLineRepresentation degree)
    (standardBadLineInhomogeneousH2Equiv degree coordinate.val)
    (locallyInner_standardBadLine_radical_zero degree coordinate.val coordinate.property)
  obtain ⟨cycle, cycleClass⟩ := representative
  have mixedEq := standardBadLineInnerMixedMap_representative degree coordinate cycle cycleClass
  refine (congrArg (crossedPullbackH1 homomorphism
    (leviCrossedH1Representation integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree))) mixedEq).trans ?_
  have primitiveExists : ∃ primitive : BadLineSemidirect → HomogeneousPoly degree,
      ∀ first ∈ standardBadLineEdgeSubgroup edge, ∀ second ∈ standardBadLineEdgeSubgroup edge,
        (inhomogeneousBoundaryMap (standardBadLineRepresentation degree) primitive).val first second =
          cycle.val.val first second :=
    locallyInner_cycle_boundary_on_edge degree edge endpointEq coordinate cycle.val cycleClass
  obtain ⟨primitive, boundary⟩ := primitiveExists
  exact mixedRestriction_zero_of_subgroup_boundary integralBadLineSplitting.conjAct
    (standardBadLineRepresentation degree) homomorphism cycle (standardBadLineEdgeSubgroup edge)
    radicalMem leviMem primitive boundary

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
