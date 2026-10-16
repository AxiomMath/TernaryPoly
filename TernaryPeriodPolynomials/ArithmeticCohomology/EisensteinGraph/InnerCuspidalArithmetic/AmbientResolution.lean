module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LineStabilizer

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {GroupType Value : Type} [Group GroupType]
  [AddCommGroup Value] [Module ℂ Value]

def ambientOrbitRepresentative (level : Subgroup GroupType) (point : GroupType) :
    GroupType :=
  (Quotient.mk'' point : MulAction.orbitRel.Quotient level GroupType).out

theorem ambientOrbitRepresentative_mul (level : Subgroup GroupType)
    (element : level) (point : GroupType) :
    ambientOrbitRepresentative level (element.val * point) =
      ambientOrbitRepresentative level point :=
  congrArg Quotient.out
    (MulAction.orbitRel.Quotient.quotient_smul_eq (g := element) (a := point))

theorem exists_ambientResolutionProjection (level : Subgroup GroupType)
    (point : GroupType) :
    ∃ element : level, element.val * ambientOrbitRepresentative level point = point := by
  apply MulAction.mem_orbit_iff.mp
  apply MulAction.orbitRel_apply.mp
  exact Quotient.exact (Quotient.out_eq
    (Quotient.mk'' point : MulAction.orbitRel.Quotient level GroupType)).symm

def ambientResolutionProjection (level : Subgroup GroupType) (point : GroupType) :
    level :=
  Classical.choose (exists_ambientResolutionProjection level point)

theorem ambientResolutionProjection_spec (level : Subgroup GroupType)
    (point : GroupType) :
    (ambientResolutionProjection level point).val *
      ambientOrbitRepresentative level point = point :=
  Classical.choose_spec (exists_ambientResolutionProjection level point)

theorem ambientResolutionProjection_mul (level : Subgroup GroupType)
    (element : level) (point : GroupType) :
    ambientResolutionProjection level (element.val * point) =
      element * ambientResolutionProjection level point := by
  apply Subtype.ext
  apply mul_right_cancel (b := ambientOrbitRepresentative level point)
  calc
    (ambientResolutionProjection level (element.val * point)).val *
        ambientOrbitRepresentative level point = element.val * point := by
      rw [← ambientOrbitRepresentative_mul level element point]
      exact ambientResolutionProjection_spec level (element.val * point)
    _ = (element * ambientResolutionProjection level point).val *
        ambientOrbitRepresentative level point := by
      change element.val * point =
        (element.val * (ambientResolutionProjection level point).val) *
          ambientOrbitRepresentative level point
      rw [mul_assoc, ambientResolutionProjection_spec]

theorem ambientMapVectorTwo {Source Target : Type} (transform : Source → Target)
    (first second : Source) :
    (fun index : Fin 2 => transform (![first, second] index)) =
      ![transform first, transform second] := by
  funext index
  fin_cases index <;> rfl

theorem ambientMapVectorThree {Source Target : Type} (transform : Source → Target)
    (first second third : Source) :
    (fun index : Fin 3 => transform (![first, second, third] index)) =
      ![transform first, transform second, transform third] := by
  funext index
  fin_cases index <;> rfl

def ambientResolutionRetraction (level : Subgroup GroupType) (point : GroupType) :
    level :=
  ambientResolutionProjection level point * (ambientResolutionProjection level 1)⁻¹

theorem ambientResolutionRetraction_mul (level : Subgroup GroupType)
    (element : level) (point : GroupType) :
    ambientResolutionRetraction level (element.val * point) =
      element * ambientResolutionRetraction level point := by
  simp only [ambientResolutionRetraction, ambientResolutionProjection_mul, mul_assoc]

theorem ambientResolutionRetraction_subtype (level : Subgroup GroupType)
    (element : level) : ambientResolutionRetraction level element.val = element := by
  have equivariance := ambientResolutionRetraction_mul level element 1
  simpa [ambientResolutionRetraction] using equivariance

def ambientRestrictionCochains (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value) (degree : ℕ) :
    cochains level representation degree →ₗ[ℂ]
      cochains (⊤ : Subgroup level) (representation.comp level.subtype) degree where
  toFun cochain :=
    ⟨fun vertices => cochain.val (fun index => (vertices index).val), by
      intro element vertices
      exact cochain.property element.val (fun index => (vertices index).val)⟩
  map_add' first second := rfl
  map_smul' scalar cochain := rfl

def ambientExtensionCochains (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value) (degree : ℕ) :
    cochains (⊤ : Subgroup level) (representation.comp level.subtype) degree →ₗ[ℂ]
      cochains level representation degree where
  toFun cochain :=
    ⟨fun vertices => cochain.val (fun index => ambientResolutionRetraction level (vertices index)), by
      intro element vertices
      have verticesEqual :
          (fun index => ambientResolutionRetraction level (element.val * vertices index)) =
            (fun index => element * ambientResolutionRetraction level (vertices index)) := by
        funext index
        exact ambientResolutionRetraction_mul level element (vertices index)
      change cochain.val (fun index => ambientResolutionRetraction level (element.val * vertices index)) = _
      rw [verticesEqual]
      exact cochain.property ⟨element, Subgroup.mem_top element⟩
        (fun index => ambientResolutionRetraction level (vertices index))⟩
  map_add' first second := rfl
  map_smul' scalar cochain := rfl

theorem ambientRestriction_extension (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value) (degree : ℕ)
    (cochain : cochains (⊤ : Subgroup level) (representation.comp level.subtype) degree) :
    ambientRestrictionCochains level representation degree
      (ambientExtensionCochains level representation degree cochain) = cochain := by
  apply Subtype.ext
  funext vertices
  change cochain.val (fun index => ambientResolutionRetraction level (vertices index).val) =
    cochain.val vertices
  simp only [ambientResolutionRetraction_subtype]

theorem ambientRestriction_differentialOne (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value)
    (cochain : cochains level representation 1) :
    ambientRestrictionCochains level representation 2
      (differentialOne level representation cochain) =
        differentialOne (⊤ : Subgroup level) (representation.comp level.subtype)
          (ambientRestrictionCochains level representation 1 cochain) := by
  apply Subtype.ext
  funext vertices
  simp only [ambientRestrictionCochains, differentialOne,
    LinearMap.coe_mk, AddHom.coe_mk, ambientMapVectorTwo]

theorem ambientExtension_differentialOne (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value)
    (cochain : cochains (⊤ : Subgroup level) (representation.comp level.subtype) 1) :
    ambientExtensionCochains level representation 2
      (differentialOne (⊤ : Subgroup level) (representation.comp level.subtype) cochain) =
        differentialOne level representation
          (ambientExtensionCochains level representation 1 cochain) := by
  apply Subtype.ext
  funext vertices
  simp only [ambientExtensionCochains, differentialOne,
    LinearMap.coe_mk, AddHom.coe_mk, ambientMapVectorTwo]

def ambientRestrictionCycles (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value) :
    cocycles level representation →ₗ[ℂ]
      cocycles (⊤ : Subgroup level) (representation.comp level.subtype) where
  toFun cycle := ⟨ambientRestrictionCochains level representation 2 cycle.val, by
    funext vertices
    have identity := congrFun cycle.property (fun index => (vertices index).val)
    simpa only [ambientRestrictionCochains, differentialTwo,
      LinearMap.coe_mk, AddHom.coe_mk, ambientMapVectorThree, Pi.zero_apply] using identity⟩
  map_add' first second := by
    apply Subtype.ext
    rfl
  map_smul' scalar cycle := by
    apply Subtype.ext
    rfl

def ambientExtensionCycles (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value) :
    cocycles (⊤ : Subgroup level) (representation.comp level.subtype) →ₗ[ℂ]
      cocycles level representation where
  toFun cycle := ⟨ambientExtensionCochains level representation 2 cycle.val, by
    funext vertices
    have identity := congrFun cycle.property
      (fun index => ambientResolutionRetraction level (vertices index))
    simpa only [ambientExtensionCochains, differentialTwo,
      LinearMap.coe_mk, AddHom.coe_mk, ambientMapVectorThree, Pi.zero_apply] using identity⟩
  map_add' first second := by
    apply Subtype.ext
    rfl
  map_smul' scalar cycle := by
    apply Subtype.ext
    rfl

theorem ambientRestriction_boundaryMap (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value)
    (cochain : cochains level representation 1) :
    ambientRestrictionCycles level representation (boundaryMap level representation cochain) =
      boundaryMap (⊤ : Subgroup level) (representation.comp level.subtype)
        (ambientRestrictionCochains level representation 1 cochain) := by
  apply Subtype.ext
  exact ambientRestriction_differentialOne level representation cochain

theorem ambientExtension_boundaryMap (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value)
    (cochain : cochains (⊤ : Subgroup level) (representation.comp level.subtype) 1) :
    ambientExtensionCycles level representation
      (boundaryMap (⊤ : Subgroup level) (representation.comp level.subtype) cochain) =
        boundaryMap level representation (ambientExtensionCochains level representation 1 cochain) := by
  apply Subtype.ext
  exact ambientExtension_differentialOne level representation cochain

def ambientResolutionPrism (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value)
    (cycle : cocycles level representation) : cochains level representation 1 :=
  ⟨fun vertices =>
    cycle.val.val ![vertices 0, (ambientResolutionRetraction level (vertices 0)).val,
      (ambientResolutionRetraction level (vertices 1)).val] -
    cycle.val.val ![vertices 0, vertices 1,
      (ambientResolutionRetraction level (vertices 1)).val], by
    intro element vertices
    have equivariance (first second third : GroupType) :
        cycle.val.val ![element.val * first, element.val * second, element.val * third] =
          representation element.val (cycle.val.val ![first, second, third]) := by
      simpa only [ambientMapVectorThree] using cycle.val.property element ![first, second, third]
    change cycle.val.val
        ![element.val * vertices 0,
          (ambientResolutionRetraction level (element.val * vertices 0)).val,
          (ambientResolutionRetraction level (element.val * vertices 1)).val] -
      cycle.val.val ![element.val * vertices 0, element.val * vertices 1,
        (ambientResolutionRetraction level (element.val * vertices 1)).val] = _
    simp only [ambientResolutionRetraction_mul, Subgroup.coe_mul]
    rw [equivariance, equivariance, map_sub]⟩

theorem ambientResolutionPrism_boundary (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value)
    (cycle : cocycles level representation) :
    ambientExtensionCycles level representation
        (ambientRestrictionCycles level representation cycle) - cycle =
      boundaryMap level representation (ambientResolutionPrism level representation cycle) := by
  apply Subtype.ext
  apply Subtype.ext
  funext vertices
  have firstIdentity := congrFun cycle.property
    ![vertices 0, vertices 1, (ambientResolutionRetraction level (vertices 1)).val,
      (ambientResolutionRetraction level (vertices 2)).val]
  have secondIdentity := congrFun cycle.property
    ![vertices 0, (ambientResolutionRetraction level (vertices 0)).val,
      (ambientResolutionRetraction level (vertices 1)).val,
      (ambientResolutionRetraction level (vertices 2)).val]
  have thirdIdentity := congrFun cycle.property
    ![vertices 0, vertices 1, vertices 2,
      (ambientResolutionRetraction level (vertices 2)).val]
  simp only [differentialTwo, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons,
    Pi.zero_apply] at firstIdentity secondIdentity thirdIdentity
  simp only [ambientExtensionCycles, ambientRestrictionCycles, ambientExtensionCochains,
    ambientRestrictionCochains, boundaryMap, differentialOne, ambientResolutionPrism,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.codRestrict_apply,
    Submodule.coe_sub, Pi.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have projectedVertices :
      (fun index => (ambientResolutionRetraction level (vertices index)).val) =
        ![(ambientResolutionRetraction level (vertices 0)).val,
          (ambientResolutionRetraction level (vertices 1)).val,
          (ambientResolutionRetraction level (vertices 2)).val] := by
    funext index
    fin_cases index <;> rfl
  rw [projectedVertices]
  change cycle.val.val
      ![(ambientResolutionRetraction level (vertices 0)).val,
        (ambientResolutionRetraction level (vertices 1)).val,
        (ambientResolutionRetraction level (vertices 2)).val] - cycle.val.val vertices =
    (cycle.val.val ![vertices 1, (ambientResolutionRetraction level (vertices 1)).val,
        (ambientResolutionRetraction level (vertices 2)).val] -
      cycle.val.val ![vertices 1, vertices 2, (ambientResolutionRetraction level (vertices 2)).val]) -
    (cycle.val.val ![vertices 0, (ambientResolutionRetraction level (vertices 0)).val,
        (ambientResolutionRetraction level (vertices 2)).val] -
      cycle.val.val ![vertices 0, vertices 2, (ambientResolutionRetraction level (vertices 2)).val]) +
    (cycle.val.val ![vertices 0, (ambientResolutionRetraction level (vertices 0)).val,
        (ambientResolutionRetraction level (vertices 1)).val] -
      cycle.val.val ![vertices 0, vertices 1, (ambientResolutionRetraction level (vertices 1)).val])
  have verticesEqual : ![vertices 0, vertices 1, vertices 2] = vertices := by
    funext index
    fin_cases index <;> rfl
  rw [verticesEqual] at thirdIdentity
  have combined := congrArg₂ (fun first second : Value => first + second)
    (congrArg₂ (fun first second : Value => first - second) secondIdentity firstIdentity)
      thirdIdentity
  apply sub_eq_zero.mp
  convert combined using 1 <;> abel

def ambientRestrictionH2 (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value) :
    H2 level representation →ₗ[ℂ]
      H2 (⊤ : Subgroup level) (representation.comp level.subtype) :=
  (LinearMap.range (boundaryMap level representation)).mapQ
    (LinearMap.range (boundaryMap (⊤ : Subgroup level) (representation.comp level.subtype)))
      (ambientRestrictionCycles level representation) (by
        rintro cycle ⟨cochain, rfl⟩
        exact ⟨ambientRestrictionCochains level representation 1 cochain,
          (ambientRestriction_boundaryMap level representation cochain).symm⟩)

def ambientExtensionH2 (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value) :
    H2 (⊤ : Subgroup level) (representation.comp level.subtype) →ₗ[ℂ]
      H2 level representation :=
  (LinearMap.range (boundaryMap (⊤ : Subgroup level) (representation.comp level.subtype))).mapQ
    (LinearMap.range (boundaryMap level representation))
      (ambientExtensionCycles level representation) (by
        rintro cycle ⟨cochain, rfl⟩
        exact ⟨ambientExtensionCochains level representation 1 cochain,
          (ambientExtension_boundaryMap level representation cochain).symm⟩)

theorem ambientExtension_restriction_H2 (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value)
    (coordinate : H2 level representation) :
    ambientExtensionH2 level representation
      (ambientRestrictionH2 level representation coordinate) = coordinate := by
  refine Quotient.inductionOn' coordinate ?_
  intro cycle
  apply (classOf_eq_iff _ _ _ _).mpr
  exact ⟨ambientResolutionPrism level representation cycle,
    (ambientResolutionPrism_boundary level representation cycle).symm⟩

theorem ambientRestriction_extension_H2 (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value)
    (coordinate : H2 (⊤ : Subgroup level) (representation.comp level.subtype)) :
    ambientRestrictionH2 level representation
      (ambientExtensionH2 level representation coordinate) = coordinate := by
  refine Quotient.inductionOn' coordinate ?_
  intro cycle
  apply congrArg (classOf (⊤ : Subgroup level) (representation.comp level.subtype))
  apply Subtype.ext
  exact ambientRestriction_extension level representation 2 cycle.val

def ambientResolutionH2Equiv (level : Subgroup GroupType)
    (representation : Representation ℂ GroupType Value) :
    H2 level representation ≃ₗ[ℂ]
      H2 (⊤ : Subgroup level) (representation.comp level.subtype) :=
  LinearEquiv.ofBijective (ambientRestrictionH2 level representation)
    ⟨Function.LeftInverse.injective (ambientExtension_restriction_H2 level representation),
      Function.RightInverse.surjective (ambientRestriction_extension_H2 level representation)⟩

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
