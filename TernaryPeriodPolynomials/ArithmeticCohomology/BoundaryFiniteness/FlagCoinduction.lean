module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.OrdinaryCohomology
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public section


namespace TernaryPeriodPolynomials.BoundaryFiniteness.FlagCoinduction

noncomputable section

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def functionAction (action : Representation ℂ G V) (X : Type) [MulAction G X] :
    Representation ℂ G (X → V) where
  toFun element :=
    { toFun := fun function input => action element (function (element⁻¹ • input))
      map_add' left right := by funext input; exact map_add (action element) _ _
      map_smul' scalar function := by funext input; exact map_smul (action element) scalar _ }
  map_one' := by ext function input; simp
  map_mul' left right := by
    ext function input
    simp only [mul_inv_rev, mul_smul, map_mul, Module.End.mul_apply,
      LinearMap.coe_mk, AddHom.coe_mk]

def toCoinduced (level : Subgroup G) (action : Representation ℂ G V) :
    (G ⧸ level → V) →ₗ[ℂ] Representation.coindV level.subtype (action.comp level.subtype) where
  toFun function := ⟨fun element => action element (function (QuotientGroup.mk element⁻¹)), by
    intro subgroupElement element
    have coset_equality :
        (QuotientGroup.mk (subgroupElement.val * element)⁻¹ : G ⧸ level) =
          QuotientGroup.mk element⁻¹ := by
      apply QuotientGroup.eq.mpr
      simpa only [inv_inv, mul_inv_cancel_right] using subgroupElement.property
    change action (subgroupElement.val * element)
      (function (QuotientGroup.mk (subgroupElement.val * element)⁻¹)) = _
    rw [coset_equality, map_mul]
    rfl⟩
  map_add' left right := by apply Subtype.ext; funext element; exact map_add (action element) _ _
  map_smul' scalar function := by
    apply Subtype.ext
    funext element
    exact map_smul (action element) scalar _

def fromCoinduced (level : Subgroup G) (action : Representation ℂ G V) :
    Representation.coindV level.subtype (action.comp level.subtype) →ₗ[ℂ] (G ⧸ level → V) where
  toFun function coset := action coset.out (function.val coset.out⁻¹)
  map_add' left right := by funext coset; exact map_add (action coset.out) _ _
  map_smul' scalar function := by funext coset; exact map_smul (action coset.out) scalar _

theorem from_to (level : Subgroup G) (action : Representation ℂ G V) (function : G ⧸ level → V) :
    fromCoinduced level action (toCoinduced level action function) = function := by
  funext coset
  change action coset.out (action coset.out⁻¹ (function (QuotientGroup.mk (coset.out⁻¹)⁻¹))) = _
  rw [inv_inv, QuotientGroup.out_eq', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem to_from (level : Subgroup G) (action : Representation ℂ G V)
    (function : Representation.coindV level.subtype (action.comp level.subtype)) :
    toCoinduced level action (fromCoinduced level action function) = function := by
  apply Subtype.ext
  funext element
  let coset : G ⧸ level := QuotientGroup.mk element⁻¹
  have membership : element * coset.out ∈ level := by
    have equality : QuotientGroup.mk element⁻¹ = coset := rfl
    rw [← Quotient.out_eq coset] at equality
    simpa only [inv_inv] using QuotientGroup.eq.mp equality
  have equivariance := function.property ⟨element * coset.out, membership⟩ coset.out⁻¹
  change action element (action coset.out (function.val coset.out⁻¹)) = function.val element
  rw [← Module.End.mul_apply, ← map_mul]
  simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, mul_inv_cancel_right] using equivariance.symm

def coefficientEquiv (level : Subgroup G) (action : Representation ℂ G V) :
    (G ⧸ level → V) ≃ₗ[ℂ] Representation.coindV level.subtype (action.comp level.subtype) :=
  LinearEquiv.ofLinearMap (toCoinduced level action) (fromCoinduced level action)
    (LinearMap.ext (to_from level action)) (LinearMap.ext (from_to level action))

theorem coefficientEquiv_intertwines (level : Subgroup G) (action : Representation ℂ G V)
    (element : G) :
    (coefficientEquiv level action).toLinearMap.comp (functionAction action (G ⧸ level) element) =
      (Representation.coind level.subtype (action.comp level.subtype) element).comp
        (coefficientEquiv level action).toLinearMap := by
  ext function argument
  change action argument (action element (function (element⁻¹ • QuotientGroup.mk argument⁻¹))) =
    action (argument * element) (function (QuotientGroup.mk (argument * element)⁻¹))
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev]
  rfl

def cohomologyEquiv (level : Subgroup G) (action : Representation ℂ G V) :
    groupCohomology.H2 (Rep.of (functionAction action (G ⧸ level))) ≃ₗ[ℂ]
      groupCohomology.H2 (Rep.of (action.comp level.subtype)) :=
  (groupCohomology.mapIso (MulEquiv.refl G) (coefficientEquiv level action)
    (coefficientEquiv_intertwines level action) 2 ≪≫
      groupCohomology.coindIso (Rep.of (action.comp level.subtype)) 2).toLinearEquiv

end

end TernaryPeriodPolynomials.BoundaryFiniteness.FlagCoinduction
