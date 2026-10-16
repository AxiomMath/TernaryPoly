module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.FreeCohomology
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section


namespace TernaryPeriodPolynomials.BoundaryFiniteness.PresentationCohomology

noncomputable section

variable {G V I : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def pullback (quotient : FreeGroup I →* G) (action : Representation ℂ G V) :
    groupCohomology.cocycles₂ (Rep.of action) →ₗ[ℂ]
      groupCohomology.cocycles₂ (Rep.of (action.comp quotient)) where
  toFun cocycle := ⟨fun pair => cocycle.val (quotient pair.1, quotient pair.2), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro left middle right
    have equation := (groupCohomology.mem_cocycles₂_iff cocycle.val).mp cocycle.property
      (quotient left) (quotient middle) (quotient right)
    simpa only [map_mul, MonoidHom.comp_apply] using equation⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def primitive (quotient : FreeGroup I →* G) (action : Representation ℂ G V) :
    groupCohomology.cocycles₂ (Rep.of action) →ₗ[ℂ] (FreeGroup I → V) :=
  (FreeCohomology.primitive (action.comp quotient)).comp (pullback quotient action)

theorem primitive_spec (quotient : FreeGroup I →* G) (action : Representation ℂ G V)
    (cocycle : groupCohomology.cocycles₂ (Rep.of action)) (left right : FreeGroup I) :
    action (quotient left) (primitive quotient action cocycle right) -
      primitive quotient action cocycle (left * right) + primitive quotient action cocycle left =
        cocycle.val (quotient left, quotient right) :=
  congrFun (FreeCohomology.primitive_spec (action.comp quotient) (pullback quotient action cocycle)) (left, right)

theorem primitive_one (quotient : FreeGroup I →* G) (action : Representation ℂ G V)
    (cocycle : groupCohomology.cocycles₂ (Rep.of action)) :
    primitive quotient action cocycle 1 = cocycle.val (1, 1) := by
  simpa only [map_one, Module.End.one_apply, one_mul, sub_self, zero_add] using
    primitive_spec quotient action cocycle 1 1

def liftPrimitive (quotient : FreeGroup I →* G) (action : Representation ℂ G V)
    (cocycle : groupCohomology.cocycles₂ (Rep.of action)) :
    FreeGroup I →* FreeCohomology.Extension action cocycle where
  toFun element := ⟨-primitive quotient action cocycle element, quotient element⟩
  map_one' := by
    apply FreeCohomology.Extension.ext
    · exact congrArg Neg.neg (primitive_one quotient action cocycle)
    · exact map_one quotient
  map_mul' left right := by
    apply FreeCohomology.Extension.ext
    · change -primitive quotient action cocycle (left * right) =
        -primitive quotient action cocycle left + action (quotient left) (-primitive quotient action cocycle right) +
          cocycle.val (quotient left, quotient right)
      rw [← primitive_spec quotient action cocycle left right, map_neg]
      abel
    · exact map_mul quotient left right

theorem boundary_of_section (action : Representation ℂ G V)
    (cocycle : groupCohomology.cocycles₂ (Rep.of action))
    (sectionMap : G →* FreeCohomology.Extension action cocycle)
    (projects : ∀ element, (sectionMap element).element = element) :
    ∃ function : G → V, (groupCohomology.d₁₂ (Rep.of action)).hom function = cocycle.val := by
  refine ⟨fun element => -(sectionMap element).vector, ?_⟩
  funext pair
  have multiplication := congrArg FreeCohomology.Extension.vector (sectionMap.map_mul pair.1 pair.2)
  change (sectionMap (pair.1 * pair.2)).vector = (sectionMap pair.1).vector +
    action (sectionMap pair.1).element (sectionMap pair.2).vector +
      cocycle.val ((sectionMap pair.1).element, (sectionMap pair.2).element) at multiplication
  rw [projects, projects] at multiplication
  change action pair.1 (-(sectionMap pair.2).vector) - (-(sectionMap (pair.1 * pair.2)).vector) +
    (-(sectionMap pair.1).vector) = cocycle.val pair
  rw [multiplication, map_neg]
  abel

theorem boundary_of_relations_vanish (quotient : FreeGroup I →* G)
    (surjective : Function.Surjective quotient) (relations : Set (FreeGroup I))
    (generates : Subgroup.normalClosure relations = quotient.ker)
    (action : Representation ℂ G V) (cocycle : groupCohomology.cocycles₂ (Rep.of action))
    (normalized : cocycle.val (1, 1) = 0)
    (vanishes : ∀ relation ∈ relations, primitive quotient action cocycle relation = 0) :
    ∃ function : G → V, (groupCohomology.d₁₂ (Rep.of action)).hom function = cocycle.val := by
  have kernel_le : quotient.ker ≤ (liftPrimitive quotient action cocycle).ker := by
    rw [← generates]
    apply Subgroup.normalClosure_le_normal
    intro relation membership
    have relation_in_kernel : relation ∈ quotient.ker := by
      rw [← generates]
      exact Subgroup.subset_normalClosure membership
    change liftPrimitive quotient action cocycle relation = 1
    apply FreeCohomology.Extension.ext
    · change -primitive quotient action cocycle relation = -cocycle.val (1, 1)
      rw [vanishes relation membership, normalized]
    · exact relation_in_kernel
  let inverse : G → FreeGroup I := fun element => Classical.choose (surjective element)
  have inverse_spec : Function.RightInverse inverse quotient := fun element => Classical.choose_spec (surjective element)
  let descended := quotient.liftOfRightInverse inverse inverse_spec ⟨liftPrimitive quotient action cocycle, kernel_le⟩
  apply boundary_of_section action cocycle descended
  intro element
  obtain ⟨word, rfl⟩ := surjective element
  have equation := quotient.liftOfRightInverse_comp_apply inverse inverse_spec
    ⟨liftPrimitive quotient action cocycle, kernel_le⟩ word
  exact congrArg FreeCohomology.Extension.element equation

def relationEvaluation (quotient : FreeGroup I →* G) (relations : Set (FreeGroup I))
    (action : Representation ℂ G V) : groupCohomology.cocycles₂ (Rep.of action) →ₗ[ℂ] V × (relations → V) where
  toFun cocycle := (cocycle.val (1, 1), fun relation => primitive quotient action cocycle relation.val)
  map_add' left right := by
    apply Prod.ext
    · rfl
    · funext relation; exact congrFun (map_add (primitive quotient action) left right) relation.val
  map_smul' scalar cocycle := by
    apply Prod.ext
    · rfl
    · funext relation; exact congrFun (map_smul (primitive quotient action) scalar cocycle) relation.val

theorem relationEvaluation_kernel_le (quotient : FreeGroup I →* G)
    (surjective : Function.Surjective quotient) (relations : Set (FreeGroup I))
    (generates : Subgroup.normalClosure relations = quotient.ker) (action : Representation ℂ G V) :
    (relationEvaluation quotient relations action).ker ≤ (groupCohomology.H2π (Rep.of action)).hom.ker := by
  intro cocycle vanishes
  have normalized : cocycle.val (1, 1) = 0 := congrArg Prod.fst vanishes
  have relation_vanishes : ∀ relation ∈ relations, primitive quotient action cocycle relation = 0 := by
    intro relation membership
    exact congrFun (congrArg Prod.snd vanishes) ⟨relation, membership⟩
  obtain ⟨function, boundary⟩ := boundary_of_relations_vanish quotient surjective relations generates
    action cocycle normalized relation_vanishes
  change (groupCohomology.H2π (Rep.of action)).hom cocycle = 0
  rw [← map_zero (groupCohomology.H2π (Rep.of action)).hom, groupCohomology.H2π_eq_iff]
  change cocycle.val - (0 : G × G → V) ∈ groupCohomology.coboundaries₂ (Rep.of action)
  rw [sub_zero]
  exact ⟨function, boundary⟩

theorem H2_finiteDimensional_of_presentation (quotient : FreeGroup I →* G)
    (surjective : Function.Surjective quotient) (relations : Set (FreeGroup I))
    (finite_relations : relations.Finite) (generates : Subgroup.normalClosure relations = quotient.ker)
    (action : Representation ℂ G V) [FiniteDimensional ℂ V] :
    FiniteDimensional ℂ (groupCohomology.H2 (Rep.of action)) := by
  let := finite_relations.to_subtype
  let evaluation := relationEvaluation quotient relations action
  let quotientMap := evaluation.ker.liftQ (groupCohomology.H2π (Rep.of action)).hom
    (relationEvaluation_kernel_le quotient surjective relations generates action)
  have quotient_finite : FiniteDimensional ℂ
      (groupCohomology.cocycles₂ (Rep.of action) ⧸ evaluation.ker) :=
    FiniteDimensional.of_injective evaluation.quotKerEquivRange.toLinearMap evaluation.quotKerEquivRange.injective
  have quotient_surjective : Function.Surjective quotientMap := by
    intro cohomologyClass
    induction cohomologyClass using groupCohomology.H2_induction_on with
    | _ cocycle => exact ⟨Submodule.Quotient.mk cocycle, rfl⟩
  exact FiniteDimensional.of_surjective quotientMap quotient_surjective

theorem H2_finiteDimensional (action : Representation ℂ G V) [Group.IsFinitelyPresented G]
    [FiniteDimensional ℂ V] : FiniteDimensional ℂ (groupCohomology.H2 (Rep.of action)) := by
  obtain ⟨_, quotient, surjective, relations, finite_relations, generates⟩ := Group.IsFinitelyPresented.out (G := G)
  exact H2_finiteDimensional_of_presentation quotient surjective relations finite_relations generates action

end

end TernaryPeriodPolynomials.BoundaryFiniteness.PresentationCohomology
