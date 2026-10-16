module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.AmbientResolution

@[expose] public section


open GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.BoundaryFiniteness.AmbientResolution

namespace TernaryPeriodPolynomials.BoundaryFiniteness.OrdinaryCohomology

noncomputable section

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem cochain_pair_translate (action : Representation ℂ G V)
    (cochain : cochains ⊤ action 1) (g a b : G) :
    cochain.val ![g * a, g * b] = action g (cochain.val ![a, b]) := by
  simpa only [map_pair] using cochain.property ⟨g, Subgroup.mem_top g⟩ ![a, b]

theorem cochain_triple_translate (action : Representation ℂ G V)
    (cochain : cochains ⊤ action 2) (g a b c : G) :
    cochain.val ![g * a, g * b, g * c] = action g (cochain.val ![a, b, c]) := by
  simpa only [map_triple] using cochain.property ⟨g, Subgroup.mem_top g⟩ ![a, b, c]

def toCycles (action : Representation ℂ G V) :
    cocycles ⊤ action →ₗ[ℂ] groupCohomology.cocycles₂ (Rep.of action) where
  toFun cocycle := ⟨fun pair => cocycle.val.val ![1, pair.1, pair.1 * pair.2], by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro g h j
    have relation := CochainHomotopy.cocycle_on_four ⊤ action cocycle 1 g (g*h) (g*(h*j))
    have translate := cochain_triple_translate action cocycle.val g 1 h (h*j)
    simp only [mul_one] at translate
    rw [translate] at relation
    change cocycle.val.val ![1, g*h, (g*h)*j] + cocycle.val.val ![1, g, g*h] =
      action g (cocycle.val.val ![1, h, h*j]) + cocycle.val.val ![1, g, g*(h*j)]
    rw [mul_assoc]
    apply sub_eq_zero.mp
    calc
      _ = -(action g (cocycle.val.val ![1, h, h*j]) -
          cocycle.val.val ![1, g*h, g*(h*j)] + cocycle.val.val ![1, g, g*(h*j)] -
          cocycle.val.val ![1, g, g*h]) := by abel
      _ = 0 := by rw [relation, neg_zero]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fromCochain (action : Representation ℂ G V) (function : G × G → V) :
    cochains ⊤ action 2 :=
  ⟨fun vertices => action (vertices 0)
    (function ((vertices 0)⁻¹ * vertices 1, (vertices 1)⁻¹ * vertices 2)), by
    intro element vertices
    change action (element.val * vertices 0)
      (function ((element.val * vertices 0)⁻¹ * (element.val * vertices 1),
        (element.val * vertices 1)⁻¹ * (element.val * vertices 2))) = _
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul, Module.End.mul_apply]⟩

def fromCycles (action : Representation ℂ G V) :
    groupCohomology.cocycles₂ (Rep.of action) →ₗ[ℂ] cocycles ⊤ action where
  toFun cocycle := ⟨fromCochain action cocycle.val, by
    funext vertices
    have relation := (groupCohomology.mem_cocycles₂_iff cocycle.val).mp cocycle.property
      ((vertices 0)⁻¹ * vertices 1) ((vertices 1)⁻¹ * vertices 2) ((vertices 2)⁻¹ * vertices 3)
    have translated := congrArg (action (vertices 0)) relation
    simp only [map_add, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left,
      mul_assoc] at translated
    change action (vertices 1) (cocycle.val ((vertices 1)⁻¹ * vertices 2, (vertices 2)⁻¹ * vertices 3)) -
      action (vertices 0) (cocycle.val ((vertices 0)⁻¹ * vertices 2, (vertices 2)⁻¹ * vertices 3)) +
      action (vertices 0) (cocycle.val ((vertices 0)⁻¹ * vertices 1, (vertices 1)⁻¹ * vertices 3)) -
      action (vertices 0) (cocycle.val ((vertices 0)⁻¹ * vertices 1, (vertices 1)⁻¹ * vertices 2)) = 0
    calc
      _ = (action (vertices 1) (cocycle.val ((vertices 1)⁻¹ * vertices 2, (vertices 2)⁻¹ * vertices 3)) +
          action (vertices 0) (cocycle.val ((vertices 0)⁻¹ * vertices 1, (vertices 1)⁻¹ * vertices 3))) -
        (action (vertices 0) (cocycle.val ((vertices 0)⁻¹ * vertices 2, (vertices 2)⁻¹ * vertices 3)) +
          action (vertices 0) (cocycle.val ((vertices 0)⁻¹ * vertices 1, (vertices 1)⁻¹ * vertices 2))) := by abel
      _ = 0 := sub_eq_zero.mpr translated.symm⟩
  map_add' left right := by
    apply Subtype.ext
    apply Subtype.ext
    funext vertices
    exact map_add (action (vertices 0)) _ _
  map_smul' scalar cocycle := by
    apply Subtype.ext
    apply Subtype.ext
    funext vertices
    exact map_smul (action (vertices 0)) scalar _

theorem to_from (action : Representation ℂ G V)
    (cocycle : groupCohomology.cocycles₂ (Rep.of action)) :
    toCycles action (fromCycles action cocycle) = cocycle := by
  apply Subtype.ext
  funext pair
  simp [toCycles, fromCycles, fromCochain]

theorem from_to (action : Representation ℂ G V) (cocycle : cocycles ⊤ action) :
    fromCycles action (toCycles action cocycle) = cocycle := by
  apply Subtype.ext
  apply Subtype.ext
  funext vertices
  change action (vertices 0)
    (cocycle.val.val ![1, (vertices 0)⁻¹ * vertices 1,
      ((vertices 0)⁻¹ * vertices 1) * ((vertices 1)⁻¹ * vertices 2)]) = cocycle.val.val vertices
  rw [mul_assoc, mul_inv_cancel_left]
  rw [← cochain_triple_translate]
  simp only [mul_one, mul_inv_cancel_left]
  apply congrArg cocycle.val.val
  funext index
  fin_cases index <;> rfl

def primitive (action : Representation ℂ G V) (function : G → V) : cochains ⊤ action 1 :=
  ⟨fun vertices => action (vertices 0) (function ((vertices 0)⁻¹ * vertices 1)), by
    intro element vertices
    change action (element.val * vertices 0)
      (function ((element.val * vertices 0)⁻¹ * (element.val * vertices 1))) = _
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul, Module.End.mul_apply]⟩

theorem to_boundary (action : Representation ℂ G V) (cochain : cochains ⊤ action 1) :
    (toCycles action (boundaryMap ⊤ action cochain)).val =
      (groupCohomology.d₁₂ (Rep.of action)).hom (fun element => cochain.val ![1, element]) := by
  funext pair
  change cochain.val ![pair.1, pair.1 * pair.2] - cochain.val ![1, pair.1 * pair.2] +
    cochain.val ![1, pair.1] =
    action pair.1 (cochain.val ![1, pair.2]) - cochain.val ![1, pair.1 * pair.2] + cochain.val ![1, pair.1]
  have translate := cochain_pair_translate action cochain pair.1 1 pair.2
  simpa only [mul_one] using congrArg
    (fun value => value - cochain.val ![1, pair.1 * pair.2] + cochain.val ![1, pair.1]) translate

theorem to_primitive_boundary (action : Representation ℂ G V) (function : G → V) :
    (toCycles action (boundaryMap ⊤ action (primitive action function))).val =
      (groupCohomology.d₁₂ (Rep.of action)).hom function := by
  rw [to_boundary]
  congr 1
  funext element
  simp [primitive]

def classMap (action : Representation ℂ G V) :
    cocycles ⊤ action →ₗ[ℂ] groupCohomology.H2 (Rep.of action) :=
  (groupCohomology.H2π (Rep.of action)).hom.comp (toCycles action)

theorem classMap_surjective (action : Representation ℂ G V) :
    Function.Surjective (classMap action) := by
  intro cohomologyClass
  induction cohomologyClass using groupCohomology.H2_induction_on with
  | _ cocycle =>
    refine ⟨fromCycles action cocycle, ?_⟩
    change (groupCohomology.H2π (Rep.of action)).hom
      (toCycles action (fromCycles action cocycle)) = _
    rw [to_from]

theorem classMap_kernel (action : Representation ℂ G V) :
    LinearMap.ker (classMap action) = LinearMap.range (boundaryMap ⊤ action) := by
  ext cocycle
  change classMap action cocycle = 0 ↔ ∃ cochain, boundaryMap ⊤ action cochain = cocycle
  have zero_class : (groupCohomology.H2π (Rep.of action)).hom 0 = 0 := map_zero _
  change (groupCohomology.H2π (Rep.of action)).hom (toCycles action cocycle) = 0 ↔ _
  rw [← zero_class, groupCohomology.H2π_eq_iff]
  change (toCycles action cocycle).val - (0 : G × G → V) ∈
    groupCohomology.coboundaries₂ (Rep.of action) ↔ _
  rw [sub_zero]
  constructor
  · rintro ⟨function, boundary⟩
    refine ⟨primitive action function, ?_⟩
    apply (Function.LeftInverse.injective (from_to action))
    apply Subtype.ext
    exact (to_primitive_boundary action function).trans boundary
  · rintro ⟨cochain, rfl⟩
    exact ⟨fun element => cochain.val ![1, element], (to_boundary action cochain).symm⟩

def groupEquiv (action : Representation ℂ G V) :
    H2 ⊤ action ≃ₗ[ℂ] groupCohomology.H2 (Rep.of action) :=
  ((LinearMap.range (boundaryMap ⊤ action)).quotEquivOfEq
    (LinearMap.ker (classMap action)) (classMap_kernel action).symm).trans
      ((classMap action).quotKerEquivOfSurjective (classMap_surjective action))

theorem groupEquiv_class (action : Representation ℂ G V) (cocycle : cocycles ⊤ action) :
    groupEquiv action (classOf ⊤ action cocycle) =
      (groupCohomology.H2π (Rep.of action)).hom (toCycles action cocycle) := rfl

def ambientEquiv (level : Subgroup G) (action : Representation ℂ G V) :
    H2 level action ≃ₗ[ℂ] groupCohomology.H2 (Rep.of (action.comp level.subtype)) :=
  (AmbientResolution.cohomologyEquiv level action).trans (groupEquiv (action.comp level.subtype))

theorem ambientEquiv_class (level : Subgroup G) (action : Representation ℂ G V)
    (cocycle : cocycles level action) :
    ambientEquiv level action (classOf level action cocycle) =
      (groupCohomology.H2π (Rep.of (action.comp level.subtype))).hom
        (toCycles (action.comp level.subtype) (restrictCycles level action cocycle)) := rfl

end

end TernaryPeriodPolynomials.BoundaryFiniteness.OrdinaryCohomology
