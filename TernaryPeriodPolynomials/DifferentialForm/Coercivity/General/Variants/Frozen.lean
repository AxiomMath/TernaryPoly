module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.FrozenMeasure
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Main
public import TernaryPeriodPolynomials.DifferentialForm.Hilbert.Basic
public import TernaryPeriodPolynomials.DifferentialForm.Compact.Adjoint

@[expose] public section


/-!
# General coercivity: consistency with the `Core` / `Hilbert` norms

For the cover `Γ(6) ∩ K` (the group `principalSixInKReal ⊆ GL₃(ℝ)`), the generic space of
compactly supported equivariant forms `CForm` is linearly isomorphic to the `TernaryPoly.PolynomialFormHilbert.Core n k`, the isomorphism `frozenEquiv` commutes with the
exterior derivative and with the explicit local adjoint, and the generic `L²` norm squared is the
square of the norm of the Hilbert completion.  Hence the target `coercivity_compact_support` is the
instance `Γ = principalSixInKReal` of the general statement, with the same objects.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MeasureTheory Set Topology TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
open scoped TernaryPoly.SymmetricSpaceRiemannian Pointwise ContDiff

/-! ### The identification of orbit spaces -/

theorem frozen_orbitRel_iff (S T : Space) :
    (MulAction.orbitRel FDeck Space) S T ↔ (MulAction.orbitRel gamma0 Space) S T := by
  rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
    MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨toGamma g, hg⟩
  · rintro ⟨γ, hγ⟩
    obtain ⟨g, rfl⟩ := toGamma_surjective γ
    exact ⟨g, hγ⟩

/-- The orbit space is homeomorphic to the generic orbit space of the same group. -/
def orbitHomeo : FOrbit ≃ₜ OrbitSpace gamma0 where
  toFun := Quotient.map (sa := MulAction.orbitRel FDeck Space) (sb := MulAction.orbitRel gamma0 Space)
    id (fun S T h => (frozen_orbitRel_iff S T).mp h)
  invFun := Quotient.map (sa := MulAction.orbitRel gamma0 Space) (sb := MulAction.orbitRel FDeck Space)
    id (fun S T h => (frozen_orbitRel_iff S T).mpr h)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h S => rfl
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h S => rfl
  continuous_toFun :=
    Continuous.quotient_map' (s := MulAction.orbitRel FDeck Space)
      (t := MulAction.orbitRel gamma0 Space) continuous_id _
  continuous_invFun :=
    Continuous.quotient_map' (s := MulAction.orbitRel gamma0 Space)
      (t := MulAction.orbitRel FDeck Space) continuous_id _

theorem orbitHomeo_proj (S : Space) :
    orbitHomeo (TernaryPoly.SymmetricSpaceCovering.quotientProjection S) = proj gamma0 S := rfl

theorem orbitHomeo_coordProj (x : Coordinates) :
    orbitHomeo (TernaryPoly.SmoothCoveringDeRham.coordinateProjection x) = coordProj gamma0 x :=
  rfl

/-! ### Forms -/

section Forms

variable {n k : ℕ}

/-- The underlying function of a compactly supported form. -/
abbrev fnF (a : TernaryPoly.PolynomialFormHilbert.Core n k) :
    Coordinates → TernaryPoly.PolynomialFormMetric.FormValue n k :=
  a.val.val.val

theorem frozen_isEquivariant_iff (w : Coordinates → TernaryPoly.PolynomialFormMetric.FormValue n k) :
    TernaryPoly.SmoothCoveringDeRham.IsEquivariant
        (TernaryPoly.PolynomialCoefficientMetric.deckRepresentation n)
        (Set.univ : Set TernaryPoly.SymmetricSpaceCovering.OrbitSpace) w ↔
      IsEquivariant gamma0 n k w := by
  constructor
  · intro h γ x hx
    obtain ⟨g, rfl⟩ := toGamma_surjective γ
    exact h g x (by simpa using hx)
  · intro h g x hx
    exact h (toGamma g) x (by simpa using hx)

theorem projSupport_eq_image (w : Coordinates → TernaryPoly.PolynomialFormMetric.FormValue n k) :
    projSupport gamma0 w = orbitHomeo '' closure
      (TernaryPoly.SmoothCoveringDeRham.coordinateProjection '' Function.support w) := by
  rw [orbitHomeo.image_closure, projSupport, image_image]
  rfl

theorem frozen_compact_iff (w : Coordinates → TernaryPoly.PolynomialFormMetric.FormValue n k) :
    IsCompact (closure (TernaryPoly.SmoothCoveringDeRham.coordinateProjection ''
      Function.support w)) ↔ IsCompact (projSupport gamma0 w) := by
  rw [projSupport_eq_image]
  constructor
  · exact fun h => h.image orbitHomeo.continuous
  · intro h
    have := h.image orbitHomeo.symm.continuous
    rwa [image_image, show (fun x => orbitHomeo.symm (orbitHomeo x)) = id from
      funext orbitHomeo.symm_apply_apply, image_id] at this

/-- The compactly supported forms are the generic ones, with the same underlying functions. -/
def frozenToGeneric (n k : ℕ) : TernaryPoly.PolynomialFormHilbert.Core n k →ₗ[ℝ]
    CForm gamma0 n k where
  toFun a := ⟨⟨fnF a, by simpa only [TernaryPoly.SmoothCoveringDeRham.liftedDomain_univ] using
        TernaryPoly.SmoothLocalDeRham.Form.smooth a.val.val, fun x hx => TernaryPoly.SmoothLocalDeRham.Form.outside a.val.val (by
        simpa only [TernaryPoly.SmoothCoveringDeRham.liftedDomain_univ] using hx)⟩,
      (frozen_isEquivariant_iff _).mp a.val.property,
      (frozen_compact_iff _).mp a.property.1⟩
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

/-- The generic compactly supported forms are the ones. -/
def genericToFrozen (n k : ℕ) : CForm gamma0 n k →ₗ[ℝ]
    TernaryPoly.PolynomialFormHilbert.Core n k where
  toFun w :=
    have hs : ContDiffOn ℝ ∞ (CForm.fn w) (TernaryPoly.SmoothCoveringDeRham.liftedDomain
        (Set.univ : Set TernaryPoly.SymmetricSpaceCovering.OrbitSpace)) := by
      simpa only [TernaryPoly.SmoothCoveringDeRham.liftedDomain_univ] using CForm.smooth w
    have ho : ∀ x ∉ TernaryPoly.SmoothCoveringDeRham.liftedDomain
        (Set.univ : Set TernaryPoly.SymmetricSpaceCovering.OrbitSpace), CForm.fn w x = 0 := by
      intro x hx
      exact CForm.outside w (by simpa only [TernaryPoly.SmoothCoveringDeRham.liftedDomain_univ] using hx)
    ⟨⟨⟨CForm.fn w, hs, ho⟩, (frozen_isEquivariant_iff _).mpr (CForm.equivariant w)⟩,
      (frozen_compact_iff _).mpr (CForm.compact w), Set.subset_univ _⟩
  map_add' _ _ := Subtype.ext (Subtype.ext (Subtype.ext rfl))
  map_smul' _ _ := Subtype.ext (Subtype.ext (Subtype.ext rfl))

/-- **Consistency with the development.**  The space of compactly supported smooth
equivariant forms `Core n k` of the cover `Γ(6) ∩ K` is linearly isomorphic to the generic
`CForm principalSixInKReal n k`, with the same underlying functions. -/
def frozenEquiv (n k : ℕ) : TernaryPoly.PolynomialFormHilbert.Core n k ≃ₗ[ℝ] CForm gamma0 n k :=
  LinearEquiv.ofLinearMap (frozenToGeneric n k) (genericToFrozen n k)
    (LinearMap.ext fun _ => Subtype.ext (Subtype.ext rfl))
    (LinearMap.ext fun _ => Subtype.ext (Subtype.ext (Subtype.ext rfl)))

theorem frozenEquiv_fn (a : TernaryPoly.PolynomialFormHilbert.Core n k) :
    CForm.fn (frozenEquiv n k a) = fnF a := rfl

theorem frozenEquiv_d (a : TernaryPoly.PolynomialFormHilbert.Core n k) :
    frozenEquiv n (k + 1) (TernaryPoly.SmoothCoveringDeRham.compactDifferential
      (TernaryPoly.PolynomialCoefficientMetric.deckRepresentation n) isOpen_univ k a) =
      CForm.d gamma0 n k (frozenEquiv n k a) := by
  apply CForm.ext
  intro x hx
  have hx' : x ∈ TernaryPoly.SmoothCoveringDeRham.liftedDomain
      (Set.univ : Set TernaryPoly.SymmetricSpaceCovering.OrbitSpace) := by
    simpa using hx
  refine Eq.trans ?_ (CForm.d_apply (frozenEquiv n k a) hx).symm
  exact TernaryPoly.SmoothLocalDeRham.d_apply
    (TernaryPoly.SmoothCoveringDeRham.liftedDomain_isOpen isOpen_univ) a.val.val hx'

theorem frozenEquiv_adjoint (a : TernaryPoly.PolynomialFormHilbert.Core n (k + 1)) :
    frozenEquiv n k (TernaryPoly.PolynomialFormCoordinates.compactAdjoint n k a) =
      CForm.delta gamma0 n k (frozenEquiv n (k + 1) a) := by
  apply CForm.ext
  intro x hx
  refine Eq.trans ?_ (CForm.delta_apply admissible_principalSixInKReal (frozenEquiv n (k + 1) a) hx).symm
  exact TernaryPoly.PolynomialFormCoordinates.compactAdjoint_apply n k a hx

theorem section_gamma0 : ∃ t : Set Space, MeasurableSet t ∧ ∀ x : Space, ∃! γ : gamma0, γ • x ∈ t :=
  admissible_principalSixInKReal.exists_unique_section

theorem frozen_integral_eq (n k : ℕ) (a : TernaryPoly.PolynomialFormHilbert.Core n k) :
    ∫ q, TernaryPoly.PolynomialFormMetric.scalarPairing n k a.val a.val q
        ∂TernaryPoly.SymmetricSpaceRiemannian.orbitVolume =
      normSq (frozenEquiv n k a) := by
  have hA0 := admissible_principalSixInKReal
  have hsec := section_gamma0
  have ht := hsec.choose_spec.1
  have hu := hsec.choose_spec.2
  have hFD : IsFundamentalDomain gamma0 hsec.choose spaceVolume :=
    IsFundamentalDomain.mk' ht.nullMeasurableSet hu
  have hπ : Measurable TernaryPoly.SymmetricSpaceCovering.quotientProjection :=
    TernaryPoly.SymmetricSpaceCovering.quotientProjection_covering.continuous.measurable
  have hmeas : Measurable (TernaryPoly.PolynomialFormMetric.scalarPairing n k a.val a.val) :=
    (TernaryPoly.PolynomialFormMetric.continuous_scalarPairing n k a.val a.val).measurable
  have hmeas0 : Measurable (scalarPairing (frozenEquiv n k a) (frozenEquiv n k a)) :=
    (continuous_scalarPairing hA0 _ _).measurable
  have i1 := congrArg
    (fun μ : MeasureTheory.Measure TernaryPoly.SymmetricSpaceCovering.OrbitSpace =>
      ∫ q, TernaryPoly.PolynomialFormMetric.scalarPairing n k a.val a.val q ∂μ)
    (orbitVolume_eq_map ht hu)
  have i2 := integral_map (μ := spaceVolume.restrict hsec.choose) hπ.aemeasurable
    hmeas.aestronglyMeasurable
  have i3 : normSq (frozenEquiv n k a) = ∫ x in hsec.choose,
      scalarPairing (frozenEquiv n k a) (frozenEquiv n k a) (proj gamma0 x) ∂spaceVolume :=
    (normSq_eq _).trans (hA0.integral_quotientVolume hFD hmeas0)
  have i4 : ∫ x in hsec.choose,
      TernaryPoly.PolynomialFormMetric.scalarPairing n k a.val a.val
        (TernaryPoly.SymmetricSpaceCovering.quotientProjection x) ∂spaceVolume =
      ∫ x in hsec.choose,
        scalarPairing (frozenEquiv n k a) (frozenEquiv n k a) (proj gamma0 x) ∂spaceVolume :=
    setIntegral_congr_fun ht (fun x _ =>
      (TernaryPoly.PolynomialFormMetric.scalarPairing_projection n k a.val a.val x).trans
        (scalarPairing_proj hA0 (frozenEquiv n k a) (frozenEquiv n k a) x).symm)
  exact i1.trans (i2.trans (i4.trans i3.symm))

/-- The squared norm in the Hilbert completion is the generic `L²` norm squared. -/
theorem frozen_normSq (n k : ℕ) (a : TernaryPoly.PolynomialFormHilbert.Core n k) :
    ‖TernaryPoly.PolynomialFormHilbert.inclusion n k a‖ ^ 2 = normSq (frozenEquiv n k a) := by
  have h1 := TernaryPoly.PolynomialFormHilbert.inner_inclusion n k a a
  have h2 : inner ℝ (TernaryPoly.PolynomialFormHilbert.inclusion n k a)
      (TernaryPoly.PolynomialFormHilbert.inclusion n k a) =
      ‖TernaryPoly.PolynomialFormHilbert.inclusion n k a‖ ^ 2 := real_inner_self_eq_norm_sq _
  exact h2.symm.trans (h1.trans (frozen_integral_eq n k a))


/-- The coercivity estimate of the target `coercivity_compact_support` for the constant `c`. -/
def FrozenCoercive (n : ℕ) (c : ℝ) : Prop :=
  (∀ a : TernaryPoly.PolynomialFormHilbert.Core n 0,
    c * ‖TernaryPoly.PolynomialFormHilbert.inclusion n 0 a‖ ^ 2 ≤
      ‖TernaryPoly.PolynomialFormHilbert.inclusion n 1
        (TernaryPoly.SmoothCoveringDeRham.compactDifferential
          (TernaryPoly.PolynomialCoefficientMetric.deckRepresentation n) isOpen_univ 0 a)‖ ^ 2) ∧
    ∀ (k : ℕ) (a : TernaryPoly.PolynomialFormHilbert.Core n (k + 1)),
      c * ‖TernaryPoly.PolynomialFormHilbert.inclusion n (k + 1) a‖ ^ 2 ≤
        ‖TernaryPoly.PolynomialFormHilbert.inclusion n k
          (TernaryPoly.PolynomialFormCoordinates.compactAdjoint n k a)‖ ^ 2 +
        ‖TernaryPoly.PolynomialFormHilbert.inclusion n (k + 2)
          (TernaryPoly.SmoothCoveringDeRham.compactDifferential
            (TernaryPoly.PolynomialCoefficientMetric.deckRepresentation n) isOpen_univ (k + 1)
            a)‖ ^ 2

theorem frozen_normSq_d (n k : ℕ) (a : TernaryPoly.PolynomialFormHilbert.Core n k) :
    ‖TernaryPoly.PolynomialFormHilbert.inclusion n (k + 1)
      (TernaryPoly.SmoothCoveringDeRham.compactDifferential
        (TernaryPoly.PolynomialCoefficientMetric.deckRepresentation n) isOpen_univ k a)‖ ^ 2 =
      normSq (CForm.d gamma0 n k (frozenEquiv n k a)) :=
  (frozen_normSq n (k + 1) _).trans (congrArg normSq (frozenEquiv_d a))

theorem frozen_normSq_adjoint (n k : ℕ) (a : TernaryPoly.PolynomialFormHilbert.Core n (k + 1)) :
    ‖TernaryPoly.PolynomialFormHilbert.inclusion n k
      (TernaryPoly.PolynomialFormCoordinates.compactAdjoint n k a)‖ ^ 2 =
      normSq (CForm.delta gamma0 n k (frozenEquiv n (k + 1) a)) :=
  (frozen_normSq n k _).trans (congrArg normSq (frozenEquiv_adjoint a))

/-- **The general statement specialises to the one.**  For the cover, the estimate with constant `c` holds exactly when the general estimate `CoerciveOn n c` holds for the
group `principalSixInKReal`. -/
theorem frozenCoercive_iff (n : ℕ) (c : ℝ) :
    FrozenCoercive n c ↔ CoerciveOn n c gamma0 := by
  constructor
  · rintro ⟨h0, hk⟩
    refine ⟨fun a => ?_, fun k a => ?_⟩
    · obtain ⟨a', rfl⟩ := (frozenEquiv n 0).surjective a
      exact (congrArg (c * ·) (frozen_normSq n 0 a').symm).trans_le
        ((h0 a').trans_eq (frozen_normSq_d n 0 a'))
    · obtain ⟨a', rfl⟩ := (frozenEquiv n (k + 1)).surjective a
      exact (congrArg (c * ·) (frozen_normSq n (k + 1) a').symm).trans_le
        ((hk k a').trans_eq (congrArg₂ (· + ·) (frozen_normSq_adjoint n k a')
          (frozen_normSq_d n (k + 1) a')))
  · rintro ⟨h0, hk⟩
    refine ⟨fun a => ?_, fun k a => ?_⟩
    · exact (congrArg (c * ·) (frozen_normSq n 0 a)).trans_le
        ((h0 (frozenEquiv n 0 a)).trans_eq (frozen_normSq_d n 0 a).symm)
    · exact (congrArg (c * ·) (frozen_normSq n (k + 1) a)).trans_le
        ((hk k (frozenEquiv n (k + 1) a)).trans_eq (congrArg₂ (· + ·)
          (frozen_normSq_adjoint n k a).symm (frozen_normSq_d n (k + 1) a).symm))

/-- The coercivity estimate is the `principalSixInKReal` instance of the general one. -/
theorem frozen_coercivity_of_general (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ FrozenCoercive n c := by
  obtain ⟨c, hc, h⟩ := coercivity_frozen_cover n hn
  exact ⟨c, hc, (frozenCoercive_iff n c).mpr h⟩

end Forms

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
