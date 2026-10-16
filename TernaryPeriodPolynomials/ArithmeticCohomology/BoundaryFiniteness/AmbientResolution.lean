module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.CochainHomotopy
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Order.Fin.SuccAboveOrderIso

@[expose] public section


open GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryFiniteness.AmbientResolution

noncomputable section

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem map_pair {A B : Type} (map : A → B) (a b : A) :
    (fun index => map (![a, b] index)) = ![map a, map b] := by
  funext index
  fin_cases index <;> rfl

theorem map_triple {A B : Type} (map : A → B) (a b c : A) :
    (fun index => map (![a, b, c] index)) = ![map a, map b, map c] := by
  funext index
  fin_cases index <;> rfl

def normalizedRepresentative (level : Subgroup G) (coset : G ⧸ level) : G := by
  classical
  exact if coset = QuotientGroup.mk 1 then 1 else coset.out

theorem normalizedRepresentative_spec (level : Subgroup G) (coset : G ⧸ level) :
    QuotientGroup.mk (normalizedRepresentative level coset) = coset := by
  classical
  unfold normalizedRepresentative
  split_ifs with equality
  · exact equality.symm
  · exact Quotient.out_eq coset

def retract (level : Subgroup G) (vertex : G) : level :=
  ⟨vertex * normalizedRepresentative level (QuotientGroup.mk vertex⁻¹), by
    have equality := normalizedRepresentative_spec level (QuotientGroup.mk vertex⁻¹)
    have membership := QuotientGroup.eq.mp equality.symm
    simpa only [inv_inv] using membership⟩

theorem retract_equivariant (level : Subgroup G) (element : level) (vertex : G) :
    retract level (element.val * vertex) = element * retract level vertex := by
  have coset_equality :
      (QuotientGroup.mk (element.val * vertex)⁻¹ : G ⧸ level) =
        QuotientGroup.mk vertex⁻¹ := by
    apply QuotientGroup.eq.mpr
    simpa only [inv_inv, mul_inv_cancel_right] using element.property
  apply Subtype.ext
  change (element.val * vertex) * normalizedRepresentative level _ =
    element.val * (vertex * normalizedRepresentative level _)
  rw [coset_equality, mul_assoc]

theorem retract_subgroup (level : Subgroup G) (element : level) :
    retract level element.val = element := by
  classical
  have coset_equality : (QuotientGroup.mk element.val⁻¹ : G ⧸ level) = QuotientGroup.mk 1 := by
    apply QuotientGroup.eq.mpr
    simpa only [inv_inv, mul_one] using element.property
  apply Subtype.ext
  change element.val * normalizedRepresentative level _ = element.val
  simp [coset_equality, normalizedRepresentative]

def vertexHomotopy (level : Subgroup G) (action : Representation ℂ G V)
    (verticesMap : G → G)
    (equivariant : ∀ (element : level) vertex,
      verticesMap (element.val * vertex) = element.val * verticesMap vertex)
    (cocycle : cocycles level action) : cochains level action 1 :=
  ⟨fun vertices =>
    cocycle.val.val ![verticesMap (vertices 0), vertices 0, vertices 1] -
      cocycle.val.val ![verticesMap (vertices 0), verticesMap (vertices 1), vertices 1], by
    intro element vertices
    have translate (a b c : G) :
        cocycle.val.val ![element.val * a, element.val * b, element.val * c] =
          action element.val (cocycle.val.val ![a, b, c]) := by
      have equality : (fun index => element.val * ![a, b, c] index) =
          ![element.val * a, element.val * b, element.val * c] := by
        funext index
        fin_cases index <;> rfl
      exact equality ▸ cocycle.val.property element ![a, b, c]
    change cocycle.val.val ![verticesMap (element.val * vertices 0),
        element.val * vertices 0, element.val * vertices 1] -
      cocycle.val.val ![verticesMap (element.val * vertices 0),
        verticesMap (element.val * vertices 1), element.val * vertices 1] = _
    rw [equivariant, equivariant, translate, translate, map_sub]⟩

theorem vertexHomotopy_formula (level : Subgroup G) (action : Representation ℂ G V)
    (verticesMap : G → G)
    (equivariant : ∀ (element : level) vertex,
      verticesMap (element.val * vertex) = element.val * verticesMap vertex)
    (cocycle : cocycles level action) (vertices : Fin 3 → G) :
    (differentialOne level action (vertexHomotopy level action verticesMap equivariant cocycle)).val vertices =
      cocycle.val.val vertices - cocycle.val.val (verticesMap ∘ vertices) := by
  have first := CochainHomotopy.cocycle_on_four level action cocycle
    (verticesMap (vertices 0)) (vertices 0) (vertices 1) (vertices 2)
  have second := CochainHomotopy.cocycle_on_four level action cocycle
    (verticesMap (vertices 0)) (verticesMap (vertices 1)) (vertices 1) (vertices 2)
  have third := CochainHomotopy.cocycle_on_four level action cocycle
    (verticesMap (vertices 0)) (verticesMap (vertices 1)) (verticesMap (vertices 2)) (vertices 2)
  have vertices_eq : ![vertices 0, vertices 1, vertices 2] = vertices := by
    funext index
    fin_cases index <;> rfl
  have mapped_eq : ![verticesMap (vertices 0), verticesMap (vertices 1), verticesMap (vertices 2)] =
      verticesMap ∘ vertices := by
    funext index
    fin_cases index <;> rfl
  rw [vertices_eq] at first
  rw [mapped_eq] at third
  apply sub_eq_zero.mp
  calc
    _ = -((cocycle.val.val vertices -
        cocycle.val.val ![verticesMap (vertices 0), vertices 1, vertices 2] +
        cocycle.val.val ![verticesMap (vertices 0), vertices 0, vertices 2] -
        cocycle.val.val ![verticesMap (vertices 0), vertices 0, vertices 1]) -
      (cocycle.val.val ![verticesMap (vertices 1), vertices 1, vertices 2] -
        cocycle.val.val ![verticesMap (vertices 0), vertices 1, vertices 2] +
        cocycle.val.val ![verticesMap (vertices 0), verticesMap (vertices 1), vertices 2] -
        cocycle.val.val ![verticesMap (vertices 0), verticesMap (vertices 1), vertices 1]) +
      (cocycle.val.val ![verticesMap (vertices 1), verticesMap (vertices 2), vertices 2] -
        cocycle.val.val ![verticesMap (vertices 0), verticesMap (vertices 2), vertices 2] +
        cocycle.val.val ![verticesMap (vertices 0), verticesMap (vertices 1), vertices 2] -
        cocycle.val.val (verticesMap ∘ vertices))) := by
      change ((cocycle.val.val ![verticesMap (vertices 1), vertices 1, vertices 2] -
          cocycle.val.val ![verticesMap (vertices 1), verticesMap (vertices 2), vertices 2]) -
        (cocycle.val.val ![verticesMap (vertices 0), vertices 0, vertices 2] -
          cocycle.val.val ![verticesMap (vertices 0), verticesMap (vertices 2), vertices 2]) +
        (cocycle.val.val ![verticesMap (vertices 0), vertices 0, vertices 1] -
          cocycle.val.val ![verticesMap (vertices 0), verticesMap (vertices 1), vertices 1])) -
        (cocycle.val.val vertices - cocycle.val.val (verticesMap ∘ vertices)) = _
      abel
    _ = 0 := by rw [first, second, third]; simp

def restrictCochain (level : Subgroup G) (action : Representation ℂ G V) (degree : ℕ) :
    cochains level action degree →ₗ[ℂ] cochains ⊤ (action.comp level.subtype) degree where
  toFun cochain := ⟨fun vertices => cochain.val (fun index => (vertices index).val), by
    intro element vertices
    exact cochain.property element.val (fun index => (vertices index).val)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extendCochain (level : Subgroup G) (action : Representation ℂ G V) (degree : ℕ) :
    cochains ⊤ (action.comp level.subtype) degree →ₗ[ℂ] cochains level action degree where
  toFun cochain := ⟨fun vertices => cochain.val (retract level ∘ vertices), by
    intro element vertices
    change cochain.val (fun index => retract level (element.val * vertices index)) = _
    simp only [retract_equivariant]
    exact cochain.property ⟨element, Subgroup.mem_top element⟩ (retract level ∘ vertices)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrict_differential (level : Subgroup G) (action : Representation ℂ G V)
    (cochain : cochains level action 1) :
    restrictCochain level action 2 (differentialOne level action cochain) =
      differentialOne ⊤ (action.comp level.subtype) (restrictCochain level action 1 cochain) := by
  apply Subtype.ext
  funext vertices
  simp [restrictCochain, differentialOne, map_pair]

theorem extend_differential (level : Subgroup G) (action : Representation ℂ G V)
    (cochain : cochains ⊤ (action.comp level.subtype) 1) :
    extendCochain level action 2 (differentialOne ⊤ (action.comp level.subtype) cochain) =
      differentialOne level action (extendCochain level action 1 cochain) := by
  apply Subtype.ext
  funext vertices
  simp [extendCochain, differentialOne, Function.comp_def, map_pair]

def restrictCycles (level : Subgroup G) (action : Representation ℂ G V) :
    cocycles level action →ₗ[ℂ] cocycles ⊤ (action.comp level.subtype) where
  toFun cocycle := ⟨restrictCochain level action 2 cocycle.val, by
    funext vertices
    simpa [restrictCochain, differentialTwo, map_triple] using
      congrFun cocycle.property (fun index => (vertices index).val)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extendCycles (level : Subgroup G) (action : Representation ℂ G V) :
    cocycles ⊤ (action.comp level.subtype) →ₗ[ℂ] cocycles level action where
  toFun cocycle := ⟨extendCochain level action 2 cocycle.val, by
    funext vertices
    simpa [extendCochain, differentialTwo, Function.comp_def, map_triple] using
      congrFun cocycle.property (retract level ∘ vertices)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrict_boundary (level : Subgroup G) (action : Representation ℂ G V)
    (cochain : cochains level action 1) :
    restrictCycles level action (boundaryMap level action cochain) =
      boundaryMap ⊤ (action.comp level.subtype) (restrictCochain level action 1 cochain) := by
  apply Subtype.ext
  exact restrict_differential level action cochain

theorem extend_boundary (level : Subgroup G) (action : Representation ℂ G V)
    (cochain : cochains ⊤ (action.comp level.subtype) 1) :
    extendCycles level action (boundaryMap ⊤ (action.comp level.subtype) cochain) =
      boundaryMap level action (extendCochain level action 1 cochain) := by
  apply Subtype.ext
  exact extend_differential level action cochain

def restriction (level : Subgroup G) (action : Representation ℂ G V) :
    H2 level action →ₗ[ℂ] H2 ⊤ (action.comp level.subtype) :=
  (LinearMap.range (boundaryMap level action)).mapQ
    (LinearMap.range (boundaryMap ⊤ (action.comp level.subtype)))
    (restrictCycles level action) (by
      rintro _ ⟨cochain, rfl⟩
      exact ⟨restrictCochain level action 1 cochain, (restrict_boundary level action cochain).symm⟩)

def extension (level : Subgroup G) (action : Representation ℂ G V) :
    H2 ⊤ (action.comp level.subtype) →ₗ[ℂ] H2 level action :=
  (LinearMap.range (boundaryMap ⊤ (action.comp level.subtype))).mapQ
    (LinearMap.range (boundaryMap level action)) (extendCycles level action) (by
      rintro _ ⟨cochain, rfl⟩
      exact ⟨extendCochain level action 1 cochain, (extend_boundary level action cochain).symm⟩)

theorem restriction_class (level : Subgroup G) (action : Representation ℂ G V)
    (cocycle : cocycles level action) :
    restriction level action (classOf level action cocycle) =
      classOf ⊤ (action.comp level.subtype) (restrictCycles level action cocycle) := rfl

theorem extension_class (level : Subgroup G) (action : Representation ℂ G V)
    (cocycle : cocycles ⊤ (action.comp level.subtype)) :
    extension level action (classOf ⊤ (action.comp level.subtype) cocycle) =
      classOf level action (extendCycles level action cocycle) := rfl

theorem restriction_extension (level : Subgroup G) (action : Representation ℂ G V)
    (cohomologyClass : H2 ⊤ (action.comp level.subtype)) :
    restriction level action (extension level action cohomologyClass) = cohomologyClass := by
  induction cohomologyClass using Submodule.Quotient.induction_on with
  | _ cocycle =>
    change classOf ⊤ (action.comp level.subtype)
      (restrictCycles level action (extendCycles level action cocycle)) =
        classOf ⊤ (action.comp level.subtype) cocycle
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext vertices
    change cocycle.val.val (fun index => retract level (vertices index).val) = cocycle.val.val vertices
    simp only [retract_subgroup]

theorem extension_restriction (level : Subgroup G) (action : Representation ℂ G V)
    (cohomologyClass : H2 level action) :
    extension level action (restriction level action cohomologyClass) = cohomologyClass := by
  induction cohomologyClass using Submodule.Quotient.induction_on with
  | _ cocycle =>
    change Submodule.Quotient.mk (extendCycles level action (restrictCycles level action cocycle)) =
      Submodule.Quotient.mk cocycle
    symm
    rw [Submodule.Quotient.eq]
    let verticesMap : G → G := fun vertex => (retract level vertex).val
    have equivariant : ∀ (element : level) vertex,
        verticesMap (element.val * vertex) = element.val * verticesMap vertex := by
      intro element vertex
      exact congrArg Subtype.val (retract_equivariant level element vertex)
    refine ⟨vertexHomotopy level action verticesMap equivariant cocycle, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext vertices
    exact vertexHomotopy_formula level action verticesMap equivariant cocycle vertices

def cohomologyEquiv (level : Subgroup G) (action : Representation ℂ G V) :
    H2 level action ≃ₗ[ℂ] H2 ⊤ (action.comp level.subtype) :=
  LinearEquiv.ofLinearMap (restriction level action) (extension level action)
    (LinearMap.ext (restriction_extension level action))
    (LinearMap.ext (extension_restriction level action))

end

end TernaryPeriodPolynomials.BoundaryFiniteness.AmbientResolution
