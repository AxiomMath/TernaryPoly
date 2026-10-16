module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Radical.CrossedEquiv

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {Radical Levi Value : Type} [Group Radical] [Group Levi]
  [AddCommGroup Value] [Module ℂ Value]
  (action : Levi →* MulAut Radical)
  (representation : Representation ℂ (SemidirectProduct Radical Levi action) Value)

theorem semidirect_conjugation_intertwines (element : Levi) (radical : Radical) :
    (SemidirectProduct.inr element : SemidirectProduct Radical Levi action) *
        SemidirectProduct.inl (action element⁻¹ radical) =
      SemidirectProduct.inl radical * SemidirectProduct.inr element := by
  apply SemidirectProduct.ext
  · simp [SemidirectProduct.mul_left]
  · simp [SemidirectProduct.mul_right]

def leviCrossedAction (element : Levi) :
    crossedCocycles (representation.comp SemidirectProduct.inl) →ₗ[ℂ]
      crossedCocycles (representation.comp SemidirectProduct.inl) where
  toFun cochain := ⟨fun radical =>
    representation (SemidirectProduct.inr element)
      (cochain.val (action element⁻¹ radical)), by
    intro first second
    change representation (SemidirectProduct.inr element)
        (cochain.val (action element⁻¹ (first * second))) =
      representation (SemidirectProduct.inr element)
          (cochain.val (action element⁻¹ first)) +
        representation (SemidirectProduct.inl first)
          (representation (SemidirectProduct.inr element)
            (cochain.val (action element⁻¹ second)))
    rw [map_mul, cochain.property, map_add]
    change _ + representation (SemidirectProduct.inr element)
        (representation (SemidirectProduct.inl (action element⁻¹ first))
          (cochain.val (action element⁻¹ second))) =
      _ + representation (SemidirectProduct.inl first)
        (representation (SemidirectProduct.inr element)
          (cochain.val (action element⁻¹ second)))
    rw [← Module.End.mul_apply, ← map_mul,
      semidirect_conjugation_intertwines, map_mul, Module.End.mul_apply]⟩
  map_add' first second := by
    apply Subtype.ext
    funext radical
    exact map_add _ _ _
  map_smul' scalar cochain := by
    apply Subtype.ext
    funext radical
    exact map_smul _ _ _

def leviCrossedRepresentation :
    Representation ℂ Levi (crossedCocycles (representation.comp SemidirectProduct.inl)) where
  toFun := leviCrossedAction action representation
  map_one' := by
    apply LinearMap.ext
    intro cochain
    apply Subtype.ext
    funext radical
    simp [leviCrossedAction]
  map_mul' first second := by
    apply LinearMap.ext
    intro cochain
    apply Subtype.ext
    funext radical
    simp [leviCrossedAction, mul_inv_rev, map_mul, Module.End.mul_apply]

theorem leviCrossedAction_boundary (element : Levi) (value : Value) :
    leviCrossedAction action representation element
        (crossedBoundary (representation.comp SemidirectProduct.inl) value) =
      crossedBoundary (representation.comp SemidirectProduct.inl)
        (representation (SemidirectProduct.inr element) value) := by
  apply Subtype.ext
  funext radical
  change representation (SemidirectProduct.inr element)
      (representation (SemidirectProduct.inl (action element⁻¹ radical)) value - value) =
    representation (SemidirectProduct.inl radical)
        (representation (SemidirectProduct.inr element) value) -
      representation (SemidirectProduct.inr element) value
  rw [map_sub, ← Module.End.mul_apply, ← map_mul,
    semidirect_conjugation_intertwines, map_mul, Module.End.mul_apply]

def crossedBoundaries (radicalRepresentation : Representation ℂ Radical Value) :
    Submodule ℂ (crossedCocycles radicalRepresentation) :=
  (crossedBoundary radicalRepresentation).range

abbrev CrossedH1 (radicalRepresentation : Representation ℂ Radical Value) :=
  crossedCocycles radicalRepresentation ⧸ crossedBoundaries radicalRepresentation

theorem leviCrossed_boundaries_stable (element : Levi) :
    crossedBoundaries (representation.comp SemidirectProduct.inl) ≤
      (crossedBoundaries (representation.comp SemidirectProduct.inl)).comap
        (leviCrossedRepresentation action representation element) := by
  rintro cochain ⟨value, rfl⟩
  refine ⟨representation (SemidirectProduct.inr element) value, ?_⟩
  exact (leviCrossedAction_boundary action representation element value).symm

def leviCrossedH1Representation :
    Representation ℂ Levi (CrossedH1 (representation.comp SemidirectProduct.inl)) :=
  (leviCrossedRepresentation action representation).quotient
    (crossedBoundaries (representation.comp SemidirectProduct.inl))
    (leviCrossed_boundaries_stable action representation)

theorem leviCrossedH1Representation_mk (element : Levi)
    (cochain : crossedCocycles (representation.comp SemidirectProduct.inl)) :
    leviCrossedH1Representation action representation element
        ((crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ cochain) =
      (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
        (leviCrossedAction action representation element cochain) := by
  rfl

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
