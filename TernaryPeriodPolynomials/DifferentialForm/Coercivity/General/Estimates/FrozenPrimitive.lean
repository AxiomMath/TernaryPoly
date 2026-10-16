module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.Frozen
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Descent
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.PositiveExactness

@[expose] public section


/-! # General coercivity, Tier B: the cover and its finite-index supergroups

For the cover `Γ(6) ∩ K` (`gamma0`), the vanishing of `H²_c → H²` in positive polynomial
degree is the theorem `TernaryPoly.PolynomialFormWeakSmooth.positive_degree_compact_smooth_exact`;
through the identification `frozenEquiv` of compactly supported forms it says that every closed
`ω ∈ CForm gamma0 n 2` is `d` of a smooth `gamma0`-equivariant one-form (`frozen_closed_compact_exact`).
Averaging over the finite quotient (`exists_equivariant_primitive_of_normal`) transfers this to every
group in which `gamma0` is a normal subgroup of finite index, for the untwisted action and for the
determinant twists (`closed_compact_exact_of_frozen_normal`).

Formalized by Claude Sonnet 5.5. -/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCharts
  TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open Set TernaryPoly.SymmetricSpaceCovering
open scoped ContDiff

variable {n : ℕ}

/-- **Tier B for the cover.**  Every closed compactly supported smooth two-form for
`gamma0` is the exterior derivative of a smooth `gamma0`-equivariant one-form. -/
theorem frozen_closed_compact_exact (hn : 0 < n) (ζ : CForm gamma0 n 2)
    (hζ : CForm.d gamma0 n 2 ζ = 0) :
    ∃ η : Coordinates → FormValue n 1, ContDiffOn ℝ ∞ η positiveCoordinates ∧
      (∀ x ∉ positiveCoordinates, η x = 0) ∧ IsEquivariant gamma0 n 1 η ∧
      ∀ x ∈ positiveCoordinates, extDeriv η x = CForm.fn ζ x := by
  have ha : TernaryPoly.SmoothCoveringDeRham.compactDifferential
      (TernaryPoly.PolynomialCoefficientMetric.deckRepresentation n) isOpen_univ 2
      ((frozenEquiv n 2).symm ζ) = 0 := by
    refine (frozenEquiv n (2 + 1)).injective ?_
    have e := frozenEquiv_d ((frozenEquiv n 2).symm ζ)
    exact (e.trans ((congrArg (CForm.d gamma0 n 2) (LinearEquiv.apply_symm_apply _ _)).trans hζ)).trans
      (LinearEquiv.map_zero (frozenEquiv n (2 + 1))).symm
  obtain ⟨v, hv⟩ := TernaryPoly.PolynomialFormWeakSmooth.positive_degree_compact_smooth_exact hn
    ((frozenEquiv n 2).symm ζ) ha
  refine ⟨v.val.val, ?_, ?_, ?_, ?_⟩
  · simpa only [TernaryPoly.SmoothCoveringDeRham.liftedDomain_univ] using
      TernaryPoly.SmoothLocalDeRham.Form.smooth v.val
  · intro x hx
    exact TernaryPoly.SmoothLocalDeRham.Form.outside v.val (by
      simpa only [TernaryPoly.SmoothCoveringDeRham.liftedDomain_univ] using hx)
  · exact (frozen_isEquivariant_iff _).mp v.property
  · intro x hx
    have hx' : x ∈ TernaryPoly.SmoothCoveringDeRham.liftedDomain
        (Set.univ : Set TernaryPoly.SymmetricSpaceCovering.OrbitSpace) := by simpa using hx
    have h1 : extDeriv v.val.val x = fnF ((frozenEquiv n 2).symm ζ) x := by
      have := congrArg (fun w => w.val.val x) hv
      exact (TernaryPoly.SmoothLocalDeRham.d_apply
        (TernaryPoly.SmoothCoveringDeRham.liftedDomain_isOpen isOpen_univ) v.val hx').symm.trans this
    exact h1.trans (congrArg (fun z => CForm.fn z x) (LinearEquiv.apply_symm_apply (frozenEquiv n 2) ζ))

/-! ### Restriction of compactly supported forms to a finite-index normal subgroup -/

section Restrict

variable {k : ℕ} {Γ Γ0 : Subgroup RealGL}

/-- Compact support modulo `Γ` implies compact support modulo a normal subgroup `Γ0` of finite
index (both admissible). -/
theorem isCompact_projSupport_of_finiteIndex (hΓ : Admissible Γ) (hΓ0 : Admissible Γ0)
    [(Γ0.subgroupOf Γ).Normal] [Finite (Γ ⧸ Γ0.subgroupOf Γ)]
    {w : Coordinates → FormValue n k} (hout : ∀ x ∉ positiveCoordinates, w x = 0)
    (hc : IsCompact (projSupport Γ w)) : IsCompact (projSupport Γ0 w) := by
  classical
  have := hΓ0.t2
  have : Fintype (Γ ⧸ Γ0.subgroupOf Γ) := Fintype.ofFinite _
  obtain ⟨K, hK, hQK⟩ := hΓ.exists_compact_lift hc
  let R : Finset Γ := Finset.univ.image (fun q : Γ ⧸ Γ0.subgroupOf Γ => q.out)
  let C : Set (OrbitSpace Γ0) :=
    ⋃ c ∈ R, proj Γ0 '' ((fun S : Space => c • S) '' K)
  have hCc : IsCompact C := R.finite_toSet.isCompact_biUnion fun c _ =>
    (hK.image (continuous_const_smul c)).image continuous_proj
  refine hCc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hCc.isClosed)
  rintro _ ⟨x, hx, rfl⟩
  have hxp : x ∈ positiveCoordinates := by
    by_contra hxn
    exact hx (hout x hxn)
  have hq : coordProj Γ x ∈ projSupport Γ w := subset_closure ⟨x, hx, rfl⟩
  obtain ⟨T, hT, hTq⟩ := hQK hq
  obtain ⟨γ, hγ⟩ := proj_eq_iff.mp hTq
  let c : Γ := (QuotientGroup.mk γ : Γ ⧸ Γ0.subgroupOf Γ).out
  have hcR : c ∈ R := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hmk : (QuotientGroup.mk c : Γ ⧸ Γ0.subgroupOf Γ) = QuotientGroup.mk γ :=
    QuotientGroup.out_eq' _
  have hh : c⁻¹ * γ ∈ Γ0.subgroupOf Γ := QuotientGroup.eq.mp hmk
  have hh' : γ * c⁻¹ ∈ Γ0.subgroupOf Γ := by
    have := Subgroup.Normal.conj_mem inferInstance _ hh c
    simpa [mul_assoc] using this
  have hS : (γ * c⁻¹) • (c • T) = coordinateChart.symm x := by
    rw [smul_smul, mul_assoc, inv_mul_cancel, mul_one]
    exact hγ
  have hproj : coordProj Γ0 x = proj Γ0 (c • T) := by
    have h1 := proj_smul (Γ := Γ0) (⟨((γ * c⁻¹ : Γ) : RealGL), Subgroup.mem_subgroupOf.mp hh'⟩ : Γ0)
      (c • T)
    rw [← h1]
    unfold coordProj
    rw [← hS]
    rfl
  rw [hproj]
  exact mem_iUnion₂.mpr ⟨c, hcR, ⟨c • T, ⟨T, hT, rfl⟩, rfl⟩⟩

/-- The restriction of a compactly supported `Γ`-equivariant form to a normal subgroup `Γ0` of
finite index is compactly supported and `Γ0`-equivariant. -/
def CForm.restrictNormal (hΓ : Admissible Γ) (hΓ0 : Admissible Γ0) (hle : Γ0 ≤ Γ)
    [(Γ0.subgroupOf Γ).Normal] [Finite (Γ ⧸ Γ0.subgroupOf Γ)] (w : CForm Γ n k) :
    CForm Γ0 n k :=
  ⟨w.1, isEquivariant_iff.mpr fun γ x hx =>
      isEquivariant_iff.mp w.2.1 ⟨(γ : RealGL), hle γ.2⟩ x hx,
    isCompact_projSupport_of_finiteIndex hΓ hΓ0 (fun _ hx => TernaryPoly.SmoothLocalDeRham.Form.outside w.1 hx) w.2.2⟩

theorem CForm.restrictNormal_fn (hΓ : Admissible Γ) (hΓ0 : Admissible Γ0) (hle : Γ0 ≤ Γ)
    [(Γ0.subgroupOf Γ).Normal] [Finite (Γ ⧸ Γ0.subgroupOf Γ)] (w : CForm Γ n k) :
    CForm.fn (CForm.restrictNormal hΓ hΓ0 hle w) = CForm.fn w := rfl

end Restrict

/-- **Tier B for finite-index supergroups of the cover.**  Let `Γ` be an admissible group
containing `gamma0` as a normal subgroup of finite index.  Every closed compactly supported
smooth `Γ`-equivariant two-form with values in `Sym^n` (`n > 0`) is the exterior derivative of a
smooth `Γ`-equivariant one-form. -/
theorem closed_compact_exact_of_frozen_normal (hn : 0 < n) {Γ : Subgroup RealGL}
    (hΓ : Admissible Γ) (hle : gamma0 ≤ Γ) [(gamma0.subgroupOf Γ).Normal]
    [Finite (Γ ⧸ gamma0.subgroupOf Γ)] (ζ : CForm Γ n 2) (hζ : CForm.d Γ n 2 ζ = 0) :
    ∃ η : Coordinates → FormValue n 1, ContDiffOn ℝ ∞ η positiveCoordinates ∧
      (∀ x ∉ positiveCoordinates, η x = 0) ∧ IsEquivariant Γ n 1 η ∧
      ∀ x ∈ positiveCoordinates, extDeriv η x = CForm.fn ζ x := by
  have hΓ0 := admissible_principalSixInKReal
  set ζ0 := CForm.restrictNormal hΓ hΓ0 hle ζ with hζ0
  have hc : CForm.d gamma0 n 2 ζ0 = 0 := by
    apply CForm.ext
    intro x hx
    rw [CForm.d_apply _ hx, CForm.restrictNormal_fn]
    have := congrArg (fun z => CForm.fn z x) hζ
    simp only [CForm.d_apply _ hx] at this
    exact this
  obtain ⟨η, h1, h2, h3, h4⟩ := frozen_closed_compact_exact hn ζ0 hc
  exact exists_equivariant_primitive_of_normal h1 h3 ζ.2.1 (fun x hx => h4 x hx)

/-- **Tier B for finite-index supergroups of the cover, determinant-twisted.**  A closed
compactly supported `gamma0`-form that is equivariant for the `det^{-e}`-twisted action of a
supergroup `Γ` in which `gamma0` is normal of finite index is the exterior derivative of a smooth
form equivariant for the twisted action of `Γ`. -/
theorem closed_compact_exact_twisted_of_frozen_normal (hn : 0 < n) (e : ℤ) {Γ : Subgroup RealGL}
    [(gamma0.subgroupOf Γ).Normal] [Finite (Γ ⧸ gamma0.subgroupOf Γ)]
    (ζ : CForm gamma0 n 2) (hζ : CForm.d gamma0 n 2 ζ = 0)
    (hΓ : IsTwEquivariant (detChar e) Γ n 2 (CForm.fn ζ)) :
    ∃ η : Coordinates → FormValue n 1, ContDiffOn ℝ ∞ η positiveCoordinates ∧
      (∀ x ∉ positiveCoordinates, η x = 0) ∧ IsTwEquivariant (detChar e) Γ n 1 η ∧
      ∀ x ∈ positiveCoordinates, extDeriv η x = CForm.fn ζ x := by
  obtain ⟨η, h1, h2, h3, h4⟩ := frozen_closed_compact_exact hn ζ hζ
  exact exists_twisted_primitive_of_normal e
    (fun γ hγ => admissible_principalSixInKReal.det_one γ hγ) h1 h3 hΓ h4

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
