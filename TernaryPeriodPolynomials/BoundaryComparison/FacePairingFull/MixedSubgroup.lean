module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.CentralVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Mixed.Exactness
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Mixed.Restriction

@[expose] public section


/-!
# Mixed classes restricted to a Levi subgroup: the converse of `mixedRestriction_zero_of_subgroup_boundary`

For a split extension `N ⋊ L` acting on `V` and a subgroup `B ≤ L`, the library proves
(`mixedRestriction_zero_of_subgroup_boundary`) that a radical-zero cycle which is a coboundary on
`N ⋊ B` has mixed class vanishing on `B`. This file proves the converse in the presence of a
central element of `B` acting by `-1` on the radical invariants (the situation of the standard
line: the scalar reflection): if the mixed class of a radical-zero cycle vanishes on `B`, then the
cycle is a coboundary on `N ⋊ B`. The proof applies the library's Hochschild–Serre exactness
(`mixedClass_zero_mem_inflation`) to the split extension `N ⋊ B` and kills the Levi
cohomology by the central-element argument.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

variable {Radical Levi Value : Type} [Group Radical] [Group Levi]
  [AddCommGroup Value] [Module ℂ Value]
  (action : Levi →* MulAut Radical)
  (representation : Representation ℂ (SemidirectProduct Radical Levi action) Value)
  (B : Subgroup Levi)

/-- The action restricted to the Levi subgroup. -/
def subAction : B →* MulAut Radical := action.comp B.subtype

/-- The inclusion `N ⋊ B ↪ N ⋊ L`. -/
def subInclusion : SemidirectProduct Radical B (subAction action B) →*
    SemidirectProduct Radical Levi action :=
  SemidirectProduct.map (MonoidHom.id Radical) B.subtype (fun _ => rfl)

/-- The representation pulled back to `N ⋊ B`. -/
def subRepresentation : Representation ℂ (SemidirectProduct Radical B (subAction action B)) Value :=
  representation.comp (subInclusion action B)

theorem subInclusion_inl (r : Radical) :
    subInclusion action B (SemidirectProduct.inl r) = SemidirectProduct.inl r := rfl

theorem subInclusion_inr (b : B) :
    subInclusion action B (SemidirectProduct.inr b) = SemidirectProduct.inr b.val := rfl

@[simp] theorem subInclusion_right (x : SemidirectProduct Radical B (subAction action B)) :
    (subInclusion action B x).right = x.right.val := rfl

@[simp] theorem subInclusion_left (x : SemidirectProduct Radical B (subAction action B)) :
    (subInclusion action B x).left = x.left := rfl

/-- The pulled-back radical-zero cycle on `N ⋊ B`. -/
def subCycle (cycle : radicalZeroTwoCycles action representation) :
    radicalZeroTwoCycles (subAction action B) (subRepresentation action representation B) :=
  ⟨⟨fun x y => cycle.val.val (subInclusion action B x) (subInclusion action B y), by
    intro a b c
    have h := cycle.val.property (subInclusion action B a) (subInclusion action B b)
      (subInclusion action B c)
    simpa only [map_mul, subRepresentation, MonoidHom.comp_apply] using h⟩, by
    intro r r'
    exact cycle.property r r'⟩

/-- If the mixed class vanishes on `B`, so does the mixed class of the pulled-back cycle. -/
theorem subCycle_mixedClass_zero (cycle : radicalZeroTwoCycles action representation)
    (zero : crossedPullbackH1 B.subtype (leviCrossedH1Representation action representation)
      (mixedClassMap action representation cycle) = 0) :
    mixedClassMap (subAction action B) (subRepresentation action representation B)
        (subCycle action representation B cycle) = 0 := by
  change (crossedBoundaries (leviCrossedH1Representation (subAction action B)
    (subRepresentation action representation B))).mkQ
      (mixedH1CocycleMap (subAction action B) (subRepresentation action representation B)
        (subCycle action representation B cycle)) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change (crossedBoundaries ((leviCrossedH1Representation action representation).comp
    B.subtype)).mkQ (crossedPullbackCocycles B.subtype
      (leviCrossedH1Representation action representation)
        (mixedH1CocycleMap action representation cycle)) = 0 at zero
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at zero
  obtain ⟨v, hv⟩ := zero
  refine ⟨v, ?_⟩
  apply Subtype.ext
  funext b
  exact congrArg (fun c => c.val b) hv

/-- **Converse of `mixedRestriction_zero_of_subgroup_boundary`.** Let `B ≤ Levi` be such that
`H²(B, E^N)` vanishes (`vanishing`). If the mixed class of a radical-zero cycle vanishes on `B`,
then the cycle is a coboundary on `N ⋊ B`: there is a primitive `p` whose inhomogeneous boundary
agrees with the cycle on all pairs of elements with Levi part in `B`. -/
theorem exists_primitive_of_pullback_mixed_zero_of_vanishing
    (vanishing : ∀ x : InhomogeneousH2 (semidirectInvariantRepresentation
      (subAction action B) (subRepresentation action representation B)), x = 0)
    (cycle : radicalZeroTwoCycles action representation)
    (zero : crossedPullbackH1 B.subtype (leviCrossedH1Representation action representation)
      (mixedClassMap action representation cycle) = 0) :
    ∃ p : SemidirectProduct Radical Levi action → Value,
      ∀ x y : SemidirectProduct Radical Levi action, x.right ∈ B → y.right ∈ B →
        (inhomogeneousBoundaryMap representation p).val x y = cycle.val.val x y := by
  classical
  have hmixed : mixedClassMap (subAction action B) (subRepresentation action representation B)
      (subCycle action representation B cycle) = 0 :=
    subCycle_mixedClass_zero action representation B cycle zero
  obtain ⟨c, hc⟩ := mixedClass_zero_mem_inflation (subAction action B)
    (subRepresentation action representation B) (subCycle action representation B cycle) hmixed
  have hc0 : c = 0 := vanishing c
  rw [hc0, map_zero] at hc
  have hmem : (subCycle action representation B cycle).val ∈
      inhomogeneousBoundaries (subRepresentation action representation B) :=
    (Submodule.Quotient.mk_eq_zero _).mp hc.symm
  obtain ⟨p', hp'⟩ := hmem
  let P : SemidirectProduct Radical Levi action → Value :=
    fun x => if h : x.right ∈ B then p' ⟨x.left, ⟨x.right, h⟩⟩ else 0
  refine ⟨P, ?_⟩
  intro x y hx hy
  have hxy : (x * y).right ∈ B := by
    rw [SemidirectProduct.mul_right]; exact B.mul_mem hx hy
  let x' : SemidirectProduct Radical B (subAction action B) := ⟨x.left, ⟨x.right, hx⟩⟩
  let y' : SemidirectProduct Radical B (subAction action B) := ⟨y.left, ⟨y.right, hy⟩⟩
  have hmul : (⟨(x * y).left, ⟨(x * y).right, hxy⟩⟩ :
      SemidirectProduct Radical B (subAction action B)) = x' * y' := by
    apply SemidirectProduct.ext <;> rfl
  have hPx : P x = p' x' := dite_eq_left hx
  have hPy : P y = p' y' := dite_eq_left hy
  have hPxy : P (x * y) = p' (x' * y') := by
    show (if h : (x * y).right ∈ B then p' ⟨(x * y).left, ⟨(x * y).right, h⟩⟩ else 0) = _
    rw [dite_eq_left hxy]
    exact congrArg p' hmul
  have key := congrArg (fun f => f.val x' y') hp'
  change representation x (P y) - P (x * y) + P x = cycle.val.val x y
  rw [hPx, hPy, hPxy]
  exact key


/-- Central-element form: if `B` contains a central element acting by `-1` on the radical
invariants, the vanishing hypothesis holds. -/
theorem exists_primitive_of_pullback_mixed_zero (central : B)
    (commutes : ∀ b : B, central * b = b * central)
    (actsNeg : ∀ v ∈ semidirectRadicalInvariants action representation,
      representation (SemidirectProduct.inr central.val) v = -v)
    (cycle : radicalZeroTwoCycles action representation)
    (zero : crossedPullbackH1 B.subtype (leviCrossedH1Representation action representation)
      (mixedClassMap action representation cycle) = 0) :
    ∃ p : SemidirectProduct Radical Levi action → Value,
      ∀ x y : SemidirectProduct Radical Levi action, x.right ∈ B → y.right ∈ B →
        (inhomogeneousBoundaryMap representation p).val x y = cycle.val.val x y :=
  exists_primitive_of_pullback_mixed_zero_of_vanishing action representation B
    (fun c => by
      refine inhomogeneousH2_zero_of_central_neg _ central commutes ?_ c
      intro v
      apply Subtype.ext
      exact actsNeg v.val v.property) cycle zero

end TernaryPeriodPolynomials.Argument.FacePairingFull
