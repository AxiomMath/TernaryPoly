module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Mixed.Kernel

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

abbrev BadLineSemidirect :=
  SemidirectProduct (Multiplicative (ℤ × ℤ)) (ℤˣ × binaryArithmeticLevel)
    integralBadLineSplitting.conjAct

def standardBadLineRepresentation (degree : ℕ) :
    Representation ℂ BadLineSemidirect (HomogeneousPoly degree) :=
  ((rationalCoefficientComponent degree trivialCharacter).comp
    (fixedPointLevel rationalLevel standardBadLine).subtype).comp
      standardBadLineSemidirectEquiv.toMonoidHom

theorem standardBadLineSemidirectEquiv_inl (radical : Multiplicative (ℤ × ℤ)) :
    standardBadLineSemidirectEquiv (SemidirectProduct.inl radical) =
      integralBadLineStabilizerEquiv (integralBadLineRadicalEmbedding radical) := by
  change integralBadLineStabilizerEquiv
    (integralBadLineRadicalEmbedding radical * integralBadLineLeviSection 1) = _
  rw [map_one, mul_one]

theorem standardBadLineRepresentation_radical (degree : ℕ) :
    (standardBadLineRepresentation degree).comp SemidirectProduct.inl =
      radicalRepresentation degree := by
  apply MonoidHom.ext
  intro radical
  apply LinearMap.ext
  intro polynomial
  change rationalCoefficientComponent degree trivialCharacter
    (standardBadLineSemidirectEquiv (SemidirectProduct.inl radical)).val polynomial = _
  rw [standardBadLineSemidirectEquiv_inl]
  rfl

def standardBadEdge : Edges := QuotientGroup.mk (1 : RationalGL3)

theorem standardBadEdge_endpoint : endpoint .line standardBadEdge = standardBadLine := rfl

theorem fixedPointLevel_standardBadEdge :
    fixedPointLevel rationalLevel standardBadEdge =
      rationalLevel ⊓ (planeParabolic ℚ ⊓ lineParabolic ℚ) := by
  exact congrArg (fun subgroup => rationalLevel ⊓ subgroup)
    (MulAction.stabilizer_quotient (planeParabolic ℚ ⊓ lineParabolic ℚ))

theorem standardBadLineRadical_mem_edge (radical : Multiplicative (ℤ × ℤ)) :
    (standardBadLineSemidirectEquiv (SemidirectProduct.inl radical)).val ∈
      fixedPointLevel rationalLevel standardBadEdge := by
  rw [fixedPointLevel_standardBadEdge, standardBadLineSemidirectEquiv_inl]
  refine ⟨(integralBadLineStabilizer_rational_mem
    (integralBadLineRadicalEmbedding radical)).1, ?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

def standardBadLineSemidirectCycle (degree : ℕ)
    (cycle : cocycles (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter)) :
    inhomogeneousTwoCycles (standardBadLineRepresentation degree) :=
  fullInhomogeneousCycleEquiv _
    (fullCycleEquiv standardBadLineSemidirectEquiv _
      (ambientRestrictionCycles _ _ cycle))

theorem standardBadLineInhomogeneousH2Equiv_classOf (degree : ℕ)
    (cycle : cocycles (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter)) :
    standardBadLineInhomogeneousH2Equiv degree
        (classOf (fixedPointLevel rationalLevel standardBadLine)
          (rationalCoefficientComponent degree trivialCharacter) cycle) =
      (inhomogeneousBoundaries (standardBadLineRepresentation degree)).mkQ
        (standardBadLineSemidirectCycle degree cycle) := rfl

theorem standardBadLineSemidirectCycle_apply (degree : ℕ)
    (cycle : cocycles (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter))
    (first second : BadLineSemidirect) :
    (standardBadLineSemidirectCycle degree cycle).val first second =
      cycle.val.val ![1, (standardBadLineSemidirectEquiv first).val,
        (standardBadLineSemidirectEquiv first).val *
          (standardBadLineSemidirectEquiv second).val] := by
  change cycle.val.val
    (fun index => (standardBadLineSemidirectEquiv (![1, first, first * second] index)).val) = _
  rw [ambientMapVectorThree (fun element : BadLineSemidirect =>
    (standardBadLineSemidirectEquiv element).val), map_one, map_mul]
  rfl

theorem locallyInner_standardBadLine_radical_zero (degree : ℕ)
    (coordinate : H2 (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter)) :
    coordinate ∈ locallyInnerClasses degree trivialCharacter .line standardBadLine →
      standardBadLineInhomogeneousH2Equiv degree coordinate ∈
        (radicalRestrictionH2 integralBadLineSplitting.conjAct
          (standardBadLineRepresentation degree)).ker := by
  refine Quotient.inductionOn' coordinate ?_
  intro cycle inner
  have edgeZero := (Submodule.mem_iInf
    (M := H2 (fixedPointLevel rationalLevel standardBadLine)
      (rationalCoefficientComponent degree trivialCharacter)) _).mp inner
        ⟨standardBadEdge, standardBadEdge_endpoint⟩
  change classOf (fixedPointLevel rationalLevel standardBadEdge)
    (rationalCoefficientComponent degree trivialCharacter)
    (subgroupRestrictionCycle
      (fixedPointLevel_edge_le_flag .line standardBadEdge standardBadLine standardBadEdge_endpoint)
      (rationalCoefficientComponent degree trivialCharacter) cycle) = 0 at edgeZero
  obtain ⟨primitive, primitiveBoundary⟩ := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range (boundaryMap (fixedPointLevel rationalLevel standardBadEdge)
      (rationalCoefficientComponent degree trivialCharacter)))).mp edgeZero
  change radicalRestrictionH2 integralBadLineSplitting.conjAct
    (standardBadLineRepresentation degree)
    (standardBadLineInhomogeneousH2Equiv degree
      (classOf (fixedPointLevel rationalLevel standardBadLine)
        (rationalCoefficientComponent degree trivialCharacter) cycle)) = 0
  rw [standardBadLineInhomogeneousH2Equiv_classOf]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨fun radical => primitive.val
    ![1, (standardBadLineSemidirectEquiv (SemidirectProduct.inl radical)).val], ?_⟩
  apply Subtype.ext
  funext first second
  have boundary := congrArg
    (fun cycle : cocycles (fixedPointLevel rationalLevel standardBadEdge)
      (rationalCoefficientComponent degree trivialCharacter) =>
      cycle.val.val ![1, (standardBadLineSemidirectEquiv (SemidirectProduct.inl first)).val,
        (standardBadLineSemidirectEquiv (SemidirectProduct.inl first)).val *
          (standardBadLineSemidirectEquiv (SemidirectProduct.inl second)).val]) primitiveBoundary
  have equivariance := primitive.property
    ⟨(standardBadLineSemidirectEquiv (SemidirectProduct.inl first)).val,
      standardBadLineRadical_mem_edge first⟩
    ![1, (standardBadLineSemidirectEquiv (SemidirectProduct.inl second)).val]
  rw [ambientMapVectorTwo, mul_one] at equivariance
  change primitive.val
      ![(standardBadLineSemidirectEquiv (SemidirectProduct.inl first)).val,
        (standardBadLineSemidirectEquiv (SemidirectProduct.inl first)).val *
          (standardBadLineSemidirectEquiv (SemidirectProduct.inl second)).val] -
    primitive.val ![1, (standardBadLineSemidirectEquiv (SemidirectProduct.inl first)).val *
      (standardBadLineSemidirectEquiv (SemidirectProduct.inl second)).val] +
    primitive.val ![1, (standardBadLineSemidirectEquiv (SemidirectProduct.inl first)).val] = _ at boundary
  rw [equivariance] at boundary
  change _ = (standardBadLineSemidirectCycle degree cycle).val
    (SemidirectProduct.inl first) (SemidirectProduct.inl second)
  rw [standardBadLineSemidirectCycle_apply]
  change rationalCoefficientComponent degree trivialCharacter
      (standardBadLineSemidirectEquiv (SemidirectProduct.inl first)).val
        (primitive.val ![1, (standardBadLineSemidirectEquiv (SemidirectProduct.inl second)).val]) -
    primitive.val ![1, (standardBadLineSemidirectEquiv (SemidirectProduct.inl (first * second))).val] +
    primitive.val ![1, (standardBadLineSemidirectEquiv (SemidirectProduct.inl first)).val] = _
  simpa only [map_mul, Subgroup.coe_mul, subgroupRestrictionCycle,
    subgroupRestrictionCochain, LinearMap.coe_mk, AddHom.coe_mk] using boundary

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
