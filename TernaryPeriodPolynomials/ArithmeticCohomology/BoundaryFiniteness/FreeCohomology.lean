module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.OrdinaryCohomology
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Algebra.Module.Projective

@[expose] public section


namespace TernaryPeriodPolynomials.BoundaryFiniteness.FreeCohomology

noncomputable section

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

structure Extension (action : Representation ℂ G V)
    (cocycle : groupCohomology.cocycles₂ (Rep.of action)) where
  vector : V
  element : G

@[ext] theorem Extension.ext {action : Representation ℂ G V}
    {cocycle : groupCohomology.cocycles₂ (Rep.of action)} {left right : Extension action cocycle}
    (vectors : left.vector = right.vector) (elements : left.element = right.element) : left = right := by
  cases left
  cases right
  cases vectors
  cases elements
  rfl

instance extensionGroup (action : Representation ℂ G V)
    (cocycle : groupCohomology.cocycles₂ (Rep.of action)) : Group (Extension action cocycle) where
  mul left right := ⟨left.vector + action left.element right.vector + cocycle.val (left.element, right.element),
    left.element * right.element⟩
  one := ⟨-cocycle.val (1, 1), 1⟩
  inv input := ⟨-cocycle.val (1, 1) - action input.element⁻¹ input.vector -
    cocycle.val (input.element⁻¹, input.element), input.element⁻¹⟩
  mul_assoc left middle right := by
    apply Extension.ext
    · change (left.vector + action left.element middle.vector + cocycle.val (left.element, middle.element)) +
        action (left.element * middle.element) right.vector + cocycle.val (left.element * middle.element, right.element) =
        left.vector + action left.element
          (middle.vector + action middle.element right.vector + cocycle.val (middle.element, right.element)) +
            cocycle.val (left.element, middle.element * right.element)
      have equation := (groupCohomology.mem_cocycles₂_iff cocycle.val).mp cocycle.property
        left.element middle.element right.element
      change cocycle.val (left.element * middle.element, right.element) + cocycle.val (left.element, middle.element) =
        action left.element (cocycle.val (middle.element, right.element)) +
          cocycle.val (left.element, middle.element * right.element) at equation
      simp only [map_add, map_mul, Module.End.mul_apply]
      calc
        _ = left.vector + action left.element middle.vector +
          action left.element (action middle.element right.vector) +
          (cocycle.val (left.element * middle.element, right.element) +
            cocycle.val (left.element, middle.element)) := by abel
        _ = _ := by rw [equation]; abel
    · exact mul_assoc _ _ _
  one_mul input := by
    apply Extension.ext
    · change -cocycle.val (1, 1) + action 1 input.vector + cocycle.val (1, input.element) = input.vector
      rw [map_one]
      change -cocycle.val (1, 1) + input.vector + cocycle.val (1, input.element) = input.vector
      have equation : cocycle.val (1, input.element) = cocycle.val (1, 1) :=
        groupCohomology.cocycles₂_map_one_fst cocycle input.element
      rw [equation]
      abel
    · exact one_mul _
  mul_one input := by
    apply Extension.ext
    · change input.vector + action input.element (-cocycle.val (1, 1)) +
        cocycle.val (input.element, 1) = input.vector
      have equation : cocycle.val (input.element, 1) = action input.element (cocycle.val (1, 1)) :=
        groupCohomology.cocycles₂_map_one_snd cocycle input.element
      rw [map_neg, equation]
      abel
    · exact mul_one _
  inv_mul_cancel input := by
    apply Extension.ext
    · change (-cocycle.val (1, 1) - action input.element⁻¹ input.vector -
        cocycle.val (input.element⁻¹, input.element)) + action input.element⁻¹ input.vector +
          cocycle.val (input.element⁻¹, input.element) = -cocycle.val (1, 1)
      abel
    · exact inv_mul_cancel _

def projection (action : Representation ℂ G V) (cocycle : groupCohomology.cocycles₂ (Rep.of action)) :
    Extension action cocycle →* G where
  toFun := Extension.element
  map_one' := rfl
  map_mul' _ _ := rfl

variable {I : Type}

def freeLift (action : Representation ℂ (FreeGroup I) V)
    (cocycle : groupCohomology.cocycles₂ (Rep.of action)) : FreeGroup I →* Extension action cocycle :=
  FreeGroup.lift (fun index => ⟨0, FreeGroup.of index⟩)

theorem freeLift_projection (action : Representation ℂ (FreeGroup I) V)
    (cocycle : groupCohomology.cocycles₂ (Rep.of action)) (element : FreeGroup I) :
    (freeLift action cocycle element).element = element := by
  have equality : (projection action cocycle).comp (freeLift action cocycle) = MonoidHom.id (FreeGroup I) := by
    apply FreeGroup.ext_hom
    intro index
    simp [freeLift, projection]
  exact congrArg (fun hom : FreeGroup I →* FreeGroup I => hom element) equality

theorem free_cocycle_is_boundary (action : Representation ℂ (FreeGroup I) V)
    (cocycle : groupCohomology.cocycles₂ (Rep.of action)) :
    ∃ function : FreeGroup I → V, (groupCohomology.d₁₂ (Rep.of action)).hom function = cocycle.val := by
  refine ⟨fun element => -(freeLift action cocycle element).vector, ?_⟩
  funext pair
  have multiplication := congrArg Extension.vector ((freeLift action cocycle).map_mul pair.1 pair.2)
  change (freeLift action cocycle (pair.1 * pair.2)).vector =
    (freeLift action cocycle pair.1).vector +
      action (freeLift action cocycle pair.1).element (freeLift action cocycle pair.2).vector +
        cocycle.val ((freeLift action cocycle pair.1).element, (freeLift action cocycle pair.2).element) at multiplication
  simp only [freeLift_projection] at multiplication
  change action pair.1 (-(freeLift action cocycle pair.2).vector) -
    (-(freeLift action cocycle (pair.1 * pair.2)).vector) +
      (-(freeLift action cocycle pair.1).vector) = cocycle.val pair
  rw [multiplication, map_neg]
  abel

def differential (action : Representation ℂ (FreeGroup I) V) :
    (FreeGroup I → V) →ₗ[ℂ] groupCohomology.cocycles₂ (Rep.of action) :=
  (groupCohomology.d₁₂ (Rep.of action)).hom.codRestrict _
    (fun function => groupCohomology.d₁₂_apply_mem_cocycles₂ function)

theorem differential_surjective (action : Representation ℂ (FreeGroup I) V) :
    Function.Surjective (differential action) := by
  intro cocycle
  obtain ⟨function, equation⟩ := free_cocycle_is_boundary action cocycle
  exact ⟨function, Subtype.ext equation⟩

def primitive (action : Representation ℂ (FreeGroup I) V) :
    groupCohomology.cocycles₂ (Rep.of action) →ₗ[ℂ] (FreeGroup I → V) :=
  Classical.choose ((differential action).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (differential_surjective action)))

theorem primitive_spec (action : Representation ℂ (FreeGroup I) V)
    (cocycle : groupCohomology.cocycles₂ (Rep.of action)) :
    (groupCohomology.d₁₂ (Rep.of action)).hom (primitive action cocycle) = cocycle.val := by
  have equation := Classical.choose_spec ((differential action).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (differential_surjective action)))
  exact congrArg (fun map => (map cocycle).val) equation

end

end TernaryPeriodPolynomials.BoundaryFiniteness.FreeCohomology
