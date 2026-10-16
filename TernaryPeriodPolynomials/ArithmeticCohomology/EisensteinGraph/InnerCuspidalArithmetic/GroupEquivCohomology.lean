module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.AmbientResolution

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {SourceGroup TargetGroup Value : Type}
  [Group SourceGroup] [Group TargetGroup] [AddCommGroup Value] [Module ℂ Value]

def fullCochainEquiv (equivalence : SourceGroup ≃* TargetGroup)
    (representation : Representation ℂ TargetGroup Value) (degree : ℕ) :
    cochains (⊤ : Subgroup TargetGroup) representation degree ≃ₗ[ℂ]
      cochains (⊤ : Subgroup SourceGroup)
        (representation.comp equivalence.toMonoidHom) degree where
  toFun cochain :=
    ⟨fun vertices => cochain.val (fun index => equivalence (vertices index)), by
      intro element vertices
      have verticesEqual :
          (fun index => equivalence (element.val * vertices index)) =
            (fun index => equivalence element.val * equivalence (vertices index)) := by
        funext index
        exact equivalence.map_mul _ _
      change cochain.val (fun index => equivalence (element.val * vertices index)) = _
      rw [verticesEqual]
      exact cochain.property ⟨equivalence element.val, Subgroup.mem_top _⟩
        (fun index => equivalence (vertices index))⟩
  invFun cochain :=
    ⟨fun vertices => cochain.val (fun index => equivalence.symm (vertices index)), by
      intro element vertices
      have verticesEqual :
          (fun index => equivalence.symm (element.val * vertices index)) =
            (fun index => equivalence.symm element.val * equivalence.symm (vertices index)) := by
        funext index
        exact equivalence.symm.map_mul _ _
      change cochain.val (fun index => equivalence.symm (element.val * vertices index)) = _
      rw [verticesEqual]
      simpa using cochain.property
        ⟨equivalence.symm element.val, Subgroup.mem_top _⟩
          (fun index => equivalence.symm (vertices index))⟩
  left_inv cochain := by
    apply Subtype.ext
    funext vertices
    simp only [equivalence.apply_symm_apply]
  right_inv cochain := by
    apply Subtype.ext
    funext vertices
    simp only [equivalence.symm_apply_apply]
  map_add' first second := rfl
  map_smul' scalar cochain := rfl

theorem fullCochainEquiv_differentialOne (equivalence : SourceGroup ≃* TargetGroup)
    (representation : Representation ℂ TargetGroup Value)
    (cochain : cochains (⊤ : Subgroup TargetGroup) representation 1) :
    fullCochainEquiv equivalence representation 2
      (differentialOne (⊤ : Subgroup TargetGroup) representation cochain) =
        differentialOne (⊤ : Subgroup SourceGroup)
          (representation.comp equivalence.toMonoidHom)
            (fullCochainEquiv equivalence representation 1 cochain) := by
  apply Subtype.ext
  funext vertices
  simp only [fullCochainEquiv, differentialOne, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, ambientMapVectorTwo]

theorem fullCochainEquiv_symm_differentialOne
    (equivalence : SourceGroup ≃* TargetGroup)
    (representation : Representation ℂ TargetGroup Value)
    (cochain : cochains (⊤ : Subgroup SourceGroup)
      (representation.comp equivalence.toMonoidHom) 1) :
    (fullCochainEquiv equivalence representation 2).symm
      (differentialOne (⊤ : Subgroup SourceGroup)
        (representation.comp equivalence.toMonoidHom) cochain) =
      differentialOne (⊤ : Subgroup TargetGroup) representation
        ((fullCochainEquiv equivalence representation 1).symm cochain) := by
  apply (fullCochainEquiv equivalence representation 2).injective
  rw [LinearEquiv.apply_symm_apply, fullCochainEquiv_differentialOne,
    LinearEquiv.apply_symm_apply]

def fullCycleEquiv (equivalence : SourceGroup ≃* TargetGroup)
    (representation : Representation ℂ TargetGroup Value) :
    cocycles (⊤ : Subgroup TargetGroup) representation ≃ₗ[ℂ]
      cocycles (⊤ : Subgroup SourceGroup)
        (representation.comp equivalence.toMonoidHom) where
  toFun cycle := ⟨fullCochainEquiv equivalence representation 2 cycle.val, by
    funext vertices
    have identity := congrFun cycle.property (fun index => equivalence (vertices index))
    simpa only [fullCochainEquiv, differentialTwo, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk, ambientMapVectorThree, Pi.zero_apply] using identity⟩
  invFun cycle := ⟨(fullCochainEquiv equivalence representation 2).symm cycle.val, by
    funext vertices
    have identity := congrFun cycle.property (fun index => equivalence.symm (vertices index))
    simpa only [fullCochainEquiv, differentialTwo, LinearEquiv.coe_mk,
      LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk,
      ambientMapVectorThree, Pi.zero_apply] using identity⟩
  left_inv cycle := by
    apply Subtype.ext
    exact (fullCochainEquiv equivalence representation 2).symm_apply_apply cycle.val
  right_inv cycle := by
    apply Subtype.ext
    exact (fullCochainEquiv equivalence representation 2).apply_symm_apply cycle.val
  map_add' first second := by
    apply Subtype.ext
    exact (fullCochainEquiv equivalence representation 2).map_add first.val second.val
  map_smul' scalar cycle := by
    apply Subtype.ext
    exact (fullCochainEquiv equivalence representation 2).map_smul scalar cycle.val

theorem fullCycleEquiv_boundaryMap (equivalence : SourceGroup ≃* TargetGroup)
    (representation : Representation ℂ TargetGroup Value)
    (cochain : cochains (⊤ : Subgroup TargetGroup) representation 1) :
    fullCycleEquiv equivalence representation
      (boundaryMap (⊤ : Subgroup TargetGroup) representation cochain) =
        boundaryMap (⊤ : Subgroup SourceGroup)
          (representation.comp equivalence.toMonoidHom)
            (fullCochainEquiv equivalence representation 1 cochain) := by
  apply Subtype.ext
  exact fullCochainEquiv_differentialOne equivalence representation cochain

theorem fullCycleEquiv_boundaries (equivalence : SourceGroup ≃* TargetGroup)
    (representation : Representation ℂ TargetGroup Value) :
    (LinearMap.range (boundaryMap (⊤ : Subgroup TargetGroup) representation)).map
        (fullCycleEquiv equivalence representation).toLinearMap =
      LinearMap.range (boundaryMap (⊤ : Subgroup SourceGroup)
        (representation.comp equivalence.toMonoidHom)) := by
  apply le_antisymm
  · rintro cycle ⟨previous, ⟨cochain, rfl⟩, rfl⟩
    exact ⟨fullCochainEquiv equivalence representation 1 cochain,
      (fullCycleEquiv_boundaryMap equivalence representation cochain).symm⟩
  · rintro cycle ⟨cochain, rfl⟩
    refine ⟨boundaryMap (⊤ : Subgroup TargetGroup) representation
        ((fullCochainEquiv equivalence representation 1).symm cochain),
      ⟨(fullCochainEquiv equivalence representation 1).symm cochain, rfl⟩, ?_⟩
    change fullCycleEquiv equivalence representation _ = _
    rw [fullCycleEquiv_boundaryMap, LinearEquiv.apply_symm_apply]

def fullGroupEquivH2 (equivalence : SourceGroup ≃* TargetGroup)
    (representation : Representation ℂ TargetGroup Value) :
    H2 (⊤ : Subgroup TargetGroup) representation ≃ₗ[ℂ]
      H2 (⊤ : Subgroup SourceGroup)
        (representation.comp equivalence.toMonoidHom) :=
  Submodule.Quotient.equiv _ _ (fullCycleEquiv equivalence representation)
    (fullCycleEquiv_boundaries equivalence representation)

def standardBadLineH2SemidirectEquiv (degree : ℕ) :
    H2 (fixedPointLevel rationalLevel standardBadLine)
        (rationalCoefficientComponent degree trivialCharacter) ≃ₗ[ℂ]
      H2 (⊤ : Subgroup (SemidirectProduct (Multiplicative (ℤ × ℤ))
          (ℤˣ × binaryArithmeticLevel) integralBadLineSplitting.conjAct))
        (((rationalCoefficientComponent degree trivialCharacter).comp
          (fixedPointLevel rationalLevel standardBadLine).subtype).comp
            standardBadLineSemidirectEquiv.toMonoidHom) :=
  (ambientResolutionH2Equiv (fixedPointLevel rationalLevel standardBadLine)
    (rationalCoefficientComponent degree trivialCharacter)).trans
      (fullGroupEquivH2 standardBadLineSemidirectEquiv
        ((rationalCoefficientComponent degree trivialCharacter).comp
          (fixedPointLevel rationalLevel standardBadLine).subtype))

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
