module

public import TernaryPeriodPolynomials.Topology.DualityEquivariance.FundamentalClass

@[expose] public section


/-!
# `K`-equivariance of the duality, piece (ii)(b): the twisted covering data

For `k ∈ GL₃(ℤ)` the action of `Γ(6)` on the rational gluing `Glued` twisted by conjugation,
`g ⋆ x = (k⁻¹ g k) x` (`GluedTw k`, and `BoundaryTw k` on the invariant boundary), is again a free
action with the same orbits, and the same projection `Glued → BordifiedOrbit` is a quotient
covering map for it (`twisted_whole_covering`, `twisted_boundary_covering`). The action of `k`
(`PhiW`, `PhiB`) is then an honest `Γ(6)`-equivariant map from the twisted covering data to the
untwisted one, lying over the homeomorphism `f̄_k` of the bordification (`fbarW`, `fbarBd`): this is
the "twisted pair" for which the library's naturality statements for the cap product apply
unchanged. The squares commute definitionally (`sqW`, `sqB`, `sqTw`, `sqInc`, `sqBase`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.DualityEquivariance

open CategoryTheory TernaryPoly TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPoly.SymmetricSpaceBordifiedQuotient TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceArithmeticProper
  TernaryPoly.SingularBoundaryRestriction Topology

/-- Conjugation `g ↦ k⁻¹ g k` of the normal subgroup `Γ(6)`. -/
def cjk (k : IntegralGL) : principalSix →* principalSix :=
  (MulAut.conjNormal (H := principalSix) k⁻¹).toMonoidHom

theorem cjk_val (k : IntegralGL) (g : principalSix) :
    ((cjk k g : principalSix) : IntegralGL) = k⁻¹ * g.1 * k := by
  simp [cjk]

theorem cjk_bijective (k : IntegralGL) : Function.Bijective (cjk k) :=
  (MulAut.conjNormal (H := principalSix) k⁻¹).bijective

/-- The rational gluing with the action of `Γ(6)` twisted by conjugation with `k`:
`g ⋆ x = (k⁻¹ g k) x`. -/
structure GluedTw (_k : IntegralGL) where
  val : Glued

instance (k : IntegralGL) : TopologicalSpace (GluedTw k) :=
  TopologicalSpace.induced GluedTw.val inferInstance

/-- The twisted gluing is homeomorphic to the gluing. -/
def GluedTw.homeo (k : IntegralGL) : GluedTw k ≃ₜ Glued where
  toFun := GluedTw.val
  invFun := GluedTw.mk
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 continuous_id

instance (k : IntegralGL) : MulAction principalSix (GluedTw k) where
  smul g x := ⟨(cjk k g) • x.val⟩
  one_smul x := by
    change GluedTw.mk ((cjk k 1) • x.val) = x
    rw [map_one, one_smul]
  mul_smul g h x := by
    change GluedTw.mk ((cjk k (g * h)) • x.val) = GluedTw.mk ((cjk k g) • (cjk k h) • x.val)
    rw [map_mul, mul_smul]

theorem GluedTw.smul_val (k : IntegralGL) (g : principalSix) (x : GluedTw k) :
    (g • x).val = (cjk k g) • x.val := rfl

instance (k : IntegralGL) : ContinuousConstSMul principalSix (GluedTw k) where
  continuous_const_smul g := by
    have : (fun x : GluedTw k => g • x) =
        (GluedTw.homeo k).symm ∘ (fun y : Glued => (cjk k g) • y) ∘ (GluedTw.homeo k) := rfl
    rw [this]
    exact (GluedTw.homeo k).symm.continuous.comp
      ((continuous_const_smul _).comp (GluedTw.homeo k).continuous)

instance (k : IntegralGL) : IsCancelSMul principalSix (GluedTw k) :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr (by
    intro g x hx
    have h1 : (cjk k g) • x.val = x.val := congrArg GluedTw.val hx
    have h2 := SymmetricSpaceBordifiedPrincipalSix.principalSix_fixed_eq_one
      SymmetricSpaceGluedArithmetic.compact_transporter_finite (cjk k g) x.val h1
    exact (cjk_bijective k).injective (h2.trans (map_one (cjk k)).symm))

/-- The covering projection of the twisted gluing. -/
def pTw (k : IntegralGL) : TopCat.of (GluedTw k) ⟶ TopCat.of BordifiedOrbit :=
  TopCat.ofHom ⟨fun x => projection principalSix x.val,
    (projection_continuous principalSix).comp (GluedTw.homeo k).continuous⟩

theorem twisted_whole_covering (k : IntegralGL) : IsQuotientCoveringMap (pTw k) principalSix := by
  rw [isQuotientCoveringMap_iff_isCoveringMap_and]
  refine ⟨wholeQuotientCovering.isCoveringMap.comp_homeomorph (GluedTw.homeo k),
    fun y => ?_, inferInstance, inferInstance, ?_⟩
  · obtain ⟨x, hx⟩ := wholeQuotientCovering.surjective y
    exact ⟨⟨x⟩, hx⟩
  · intro x y
    change projection principalSix x.val = projection principalSix y.val ↔ _
    rw [show projection principalSix x.val = projection principalSix y.val ↔
        x.val ∈ MulAction.orbit principalSix y.val from
      wholeQuotientCovering.apply_eq_iff_mem_orbit]
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨g', rfl⟩ := (cjk_bijective k).surjective g
      exact ⟨g', congrArg GluedTw.mk hg⟩
    · rintro ⟨g, hg⟩
      exact ⟨cjk k g, congrArg GluedTw.val hg⟩

/-! ### The twisted boundary cover -/

/-- The invariant boundary of the twisted gluing. -/
abbrev BoundaryTw (k : IntegralGL) := {x : GluedTw k // x.val ∈ upstairsBoundary}

theorem smul_mem_boundaryTw (k : IntegralGL) (g : principalSix) {x : GluedTw k}
    (hx : x.val ∈ upstairsBoundary) : (g • x).val ∈ upstairsBoundary := by
  rw [GluedTw.smul_val, boundary_iff, projection_smul]
  exact (boundary_iff _).mp hx

instance (k : IntegralGL) : MulAction principalSix (BoundaryTw k) where
  smul g x := ⟨g • x.1, smul_mem_boundaryTw k g x.2⟩
  one_smul x := Subtype.ext (one_smul principalSix x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

theorem BoundaryTw.smul_val (k : IntegralGL) (g : principalSix) (x : BoundaryTw k) :
    (g • x).1 = g • x.1 := rfl

instance (k : IntegralGL) : ContinuousConstSMul principalSix (BoundaryTw k) where
  continuous_const_smul g :=
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _

instance (k : IntegralGL) : IsCancelSMul principalSix (BoundaryTw k) :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr (by
    intro g x hx
    exact (isCancelSMul_iff_eq_one_of_smul_eq.mp inferInstance) g x.1 (congrArg Subtype.val hx))

/-- The homeomorphism of the twisted boundary cover with the boundary cover. -/
def BoundaryTw.homeo (k : IntegralGL) : BoundaryTw k ≃ₜ BoundaryCover :=
  (GluedTw.homeo k).subtype (fun _ => Iff.rfl)

/-- The covering projection of the twisted boundary cover. -/
def pbTw (k : IntegralGL) : TopCat.of (BoundaryTw k) ⟶ TopCat.of BoundaryBase :=
  TopCat.ofHom ⟨fun x => ⟨projection principalSix x.1.val, (boundary_iff _).mp x.2⟩,
    ((projection_continuous principalSix).comp ((GluedTw.homeo k).continuous.comp
      continuous_subtype_val)).subtype_mk _⟩

theorem twisted_boundary_covering (k : IntegralGL) :
    IsQuotientCoveringMap (pbTw k) principalSix := by
  rw [isQuotientCoveringMap_iff_isCoveringMap_and]
  refine ⟨boundaryCovering.comp_homeomorph (BoundaryTw.homeo k), fun y => ?_, inferInstance,
    inferInstance, ?_⟩
  · obtain ⟨x, hx⟩ := boundaryProjection_surjective y
    exact ⟨⟨⟨x.val⟩, x.property⟩, hx⟩
  · intro x y
    have key : pbTw k x = pbTw k y ↔ boundaryProjection (BoundaryTw.homeo k x) =
        boundaryProjection (BoundaryTw.homeo k y) := Iff.rfl
    rw [key, boundaryQuotientCovering.apply_eq_iff_mem_orbit]
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨g', rfl⟩ := (cjk_bijective k).surjective g
      refine ⟨g', Subtype.ext (congrArg GluedTw.mk ?_)⟩
      exact congrArg Subtype.val hg
    · rintro ⟨g, hg⟩
      exact ⟨cjk k g, Subtype.ext (congrArg GluedTw.val (congrArg Subtype.val hg))⟩


/-! ### The comparison maps between twisted and untwisted data -/

/-- Action of `k` as an equivariant map from the twisted gluing to the gluing. -/
def PhiW (k : IntegralGL) : TopCat.of (GluedTw k) ⟶ TopCat.of Glued :=
  TopCat.ofHom ⟨fun x => integralAction k x.val,
    (continuous_leftAction _).comp (GluedTw.homeo k).continuous⟩

theorem PhiW_equivariant (k : IntegralGL) (g : principalSix) (x : GluedTw k) :
    PhiW k (g • x) = g • PhiW k x := by
  change integralAction k ((cjk k g) • x.val) = g • integralAction k x.val
  change k • ((cjk k g : principalSix) • x.val) = (g : IntegralGL) • (k • x.val)
  change k • (((cjk k g : principalSix) : IntegralGL) • x.val) = _
  rw [cjk_val, ← mul_smul, ← mul_smul]
  congr 1
  group

/-- The same on the boundary covers. -/
def PhiB (k : IntegralGL) : TopCat.of (BoundaryTw k) ⟶ TopCat.of BoundaryCover :=
  TopCat.ofHom ⟨fun x => ⟨integralAction k x.1.val, by
      rw [boundary_iff]
      have h := (boundary_iff _).mp x.2
      change fbar k (projection principalSix x.1.val) ∈ boundary principalSix
      exact fbar_mem_boundary k h⟩,
    ((continuous_leftAction _).comp ((GluedTw.homeo k).continuous.comp
      continuous_subtype_val)).subtype_mk _⟩

/-- The induced homeomorphism of the bordification, as a map of spaces. -/
def fbarW (k : IntegralGL) : TopCat.of BordifiedOrbit ⟶ TopCat.of BordifiedOrbit :=
  TopCat.ofHom ⟨fbar k, (fbar k).continuous⟩

/-- The induced map of the boundary of the bordification. -/
def fbarBd (k : IntegralGL) : TopCat.of BoundaryBase ⟶ TopCat.of BoundaryBase :=
  TopCat.ofHom ⟨fun x => ⟨fbar k x.1, fbar_mem_boundary k x.2⟩,
    ((fbar k).continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The inclusion of the twisted boundary cover. -/
def incTw (k : IntegralGL) : TopCat.of (BoundaryTw k) ⟶ TopCat.of (GluedTw k) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem sqW (k : IntegralGL) : PhiW k ≫ wholeProjection = pTw k ≫ fbarW k := rfl

theorem sqB (k : IntegralGL) : PhiB k ≫ boundaryProjection = pbTw k ≫ fbarBd k := rfl

theorem sqTw (k : IntegralGL) : incTw k ≫ pTw k = pbTw k ≫ boundaryBaseInclusion := rfl

theorem sqInc (k : IntegralGL) : incTw k ≫ PhiW k = PhiB k ≫ boundaryInclusion := rfl

theorem sqBase (k : IntegralGL) : fbarBd k ≫ boundaryBaseInclusion = boundaryBaseInclusion ≫ fbarW k :=
  rfl

theorem incTw_equivariant (k : IntegralGL) (g : principalSix) (x : BoundaryTw k) :
    incTw k (g • x) = g • incTw k x := rfl

theorem PhiB_equivariant (k : IntegralGL) (g : principalSix) (x : BoundaryTw k) :
    PhiB k (g • x) = g • PhiB k x :=
  Subtype.ext (PhiW_equivariant k g x.1)

end TernaryPeriodPolynomials.Argument.DualityEquivariance
