module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Siegel
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.HodgePair
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

@[expose] public section


/-!
# A `Γ`-partition of unity on the upper half plane and equivariant primitives

For a subgroup `Γ` of `SL(2, ℤ)` and a finite set `R` of left coset representatives
(`g = r γ`, `r ∈ R`, `γ ∈ Γ`; `exists_cosetReps` for finite index), `cutoff Γ R` is a smooth
nonnegative function on the upper half plane `U` with
`∑ᶠ γ ∈ Γ, cutoff Γ R (γ⁻¹ z) = 1` (`finsum_cutoff`). Its support lies in the finitely many
translates `r⁻¹ S` of the Siegel set `S` (`mem_siegel_of_cutoff_ne_zero`), so it is NOT compactly
supported; the family of its translates is locally finite on `U` (`exists_finite_nbhd_cutoff`),
and only finitely many translates meet a compact subset of `U`
(`finite_translates_of_isCompact`).

For a `1`-cocycle `c(δγ) = c(δ) + ρ(δ) c(γ)` the function
`primitive Γ R c z = ∑ᶠ γ, cutoff Γ R (γ⁻¹ z) • c γ` is smooth on `U` (`contDiffOn_primitive`)
and satisfies `φ(δ z) = ρ(δ) φ(z) + c(δ)` (`primitive_mob`). This is the equivariant primitive
of the Eichler–Shimura surjectivity route (Section 6 of the paper). Here smooth means
`ContDiffOn ℝ ∞`; note that `ContDiffOn ℝ ⊤` is analyticity in current Mathlib.

The Möbius action on `ℂ` is `mob g z = g • ofComplex z`, which agrees with
`(a z + b)/(c z + d)` on `U` (`mob_eq`).

Written by Claude Opus 5.5.
-/

open UpperHalfPlane ModularGroup Complex
open scoped Modular MatrixGroups ContDiff
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)
open Function (support)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.Partition

open TernaryPeriodPolynomials.Argument.ESFoundations (siegel finite_strip)

/-! ### The Möbius action on `ℂ` -/

/-- The Möbius action of `SL(2, ℤ)` on `ℂ`, through the upper half plane. -/
def mob (g : SL(2, ℤ)) (z : ℂ) : ℂ := ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)

theorem mob_mem (g : SL(2, ℤ)) (z : ℂ) : mob g z ∈ U :=
  (g • UpperHalfPlane.ofComplex z).im_pos

theorem mapsTo_mob (g : SL(2, ℤ)) : Set.MapsTo (mob g) U U := fun z _ => mob_mem g z

theorem mob_coe (g : SL(2, ℤ)) (w : ℍ) : mob g w = ((g • w : ℍ) : ℂ) := by
  rw [mob, UpperHalfPlane.ofComplex_apply]

theorem mob_mul (g h : SL(2, ℤ)) (z : ℂ) : mob (g * h) z = mob g (mob h z) := by
  rw [mob, mob, mob, mul_smul, UpperHalfPlane.ofComplex_apply]

theorem mob_one {z : ℂ} (hz : z ∈ U) : mob 1 z = z := by
  rw [mob, one_smul, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem denom_ne_zero' (g : SL(2, ℤ)) {z : ℂ} (hz : z ∈ U) :
    ((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ) ≠ 0 := by
  have := UpperHalfPlane.denom_ne_zero g ⟨z, hz⟩
  rw [ModularGroup.denom_apply] at this
  exact_mod_cast this

theorem mob_eq (g : SL(2, ℤ)) {z : ℂ} (hz : z ∈ U) :
    mob g z = (((g 0 0 : ℤ) : ℂ) * z + ((g 0 1 : ℤ) : ℂ)) /
      (((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ)) := by
  rw [mob, UpperHalfPlane.ofComplex_apply_of_im_pos hz, UpperHalfPlane.specialLinearGroup_apply]
  simp

theorem contDiffOn_mob (g : SL(2, ℤ)) {n : WithTop ℕ∞} : ContDiffOn ℝ n (mob g) U := by
  have hnum : ContDiff ℂ n fun z : ℂ => ((g 0 0 : ℤ) : ℂ) * z + ((g 0 1 : ℤ) : ℂ) :=
    (contDiff_const.mul contDiff_id).add contDiff_const
  have hden : ContDiff ℂ n fun z : ℂ => ((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ) :=
    (contDiff_const.mul contDiff_id).add contDiff_const
  have h := ContDiffOn.div hnum.contDiffOn hden.contDiffOn fun z hz => denom_ne_zero' g hz
  exact (h.restrict_scalars ℝ).congr fun z hz => mob_eq g hz

/-! ### The bump function -/

/-- A smooth bump, positive exactly on `|Re z| < 1`, `Im z > 1/2`. -/
def bump (z : ℂ) : ℝ :=
  Real.smoothTransition (1 - z.re ^ 2) * Real.smoothTransition (2 * z.im - 1)

theorem contDiff_bump : ContDiff ℝ ∞ bump := by
  have h1 : ContDiff ℝ ∞ fun z : ℂ => 1 - z.re ^ 2 :=
    contDiff_const.sub (Complex.reCLM.contDiff.pow 2)
  have h2 : ContDiff ℝ ∞ fun z : ℂ => 2 * z.im - 1 :=
    (contDiff_const.mul Complex.imCLM.contDiff).sub contDiff_const
  exact (Real.smoothTransition.contDiff.comp h1).mul (Real.smoothTransition.contDiff.comp h2)

theorem bump_nonneg (z : ℂ) : 0 ≤ bump z :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem mem_of_bump_ne_zero {z : ℂ} (h : bump z ≠ 0) : |z.re| ≤ 1 ∧ 1 / 2 ≤ z.im := by
  have h1 : 0 < 1 - z.re ^ 2 := by
    by_contra h'
    exact h (by rw [bump, Real.smoothTransition.zero_of_nonpos (not_lt.mp h'), zero_mul])
  have h2 : 0 < 2 * z.im - 1 := by
    by_contra h'
    exact h (by rw [bump, Real.smoothTransition.zero_of_nonpos (not_lt.mp h'), mul_zero])
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, by linarith⟩ <;> nlinarith [sq_nonneg (z.re + 1), sq_nonneg (z.re - 1)]

theorem bump_pos_of_mem_fd {w : ℍ} (hw : w ∈ 𝒟) : 0 < bump w := by
  have h1 : |w.re| ≤ 1 / 2 := hw.2
  have h2 := three_le_four_mul_im_sq_of_mem_fd hw
  have h3 := w.im_pos
  obtain ⟨h4, h5⟩ := abs_le.mp h1
  refine mul_pos (Real.smoothTransition.pos_of_pos ?_) (Real.smoothTransition.pos_of_pos ?_)
  · change 0 < 1 - w.re ^ 2
    nlinarith
  · change 0 < 2 * w.im - 1
    nlinarith

/-! ### Local finiteness -/

/-- Around each point of `U` there is a neighbourhood and a finite set `T` containing every `g`
that moves a point of the neighbourhood into the Siegel set. -/
theorem exists_finite_nbhd {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧ ∃ T : Finset SL(2, ℤ), ∀ z ∈ V, ∀ g : SL(2, ℤ),
      (|(mob g z).re| ≤ 1 ∧ 1 / 2 ≤ (mob g z).im) → g ∈ T := by
  have hy : 0 < z₀.im := hz₀
  set r := z₀.im / 2 with hr
  have hr0 : 0 < r := by positivity
  have hball : ∀ z ∈ Metric.ball z₀ r, r ≤ z.im ∧ z.im ≤ 3 * r ∧ |z.re| ≤ |z₀.re| + r := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have him := Complex.abs_im_le_norm (z - z₀)
    have hre := Complex.abs_re_le_norm (z - z₀)
    rw [Complex.sub_im] at him
    rw [Complex.sub_re] at hre
    obtain ⟨h1, h2⟩ := abs_le.mp him
    refine ⟨by linarith, by linarith, ?_⟩
    have := abs_sub_abs_le_abs_sub z.re z₀.re
    linarith
  have hfin := finite_strip hr0 (3 * r) (|z₀.re| + r)
  refine ⟨Metric.ball z₀ r, Metric.isOpen_ball, Metric.mem_ball_self hr0, ?_,
    hfin.toFinset, ?_⟩
  · intro z hz
    show 0 < z.im
    linarith [(hball z hz).1]
  · intro z hz g hg
    obtain ⟨h1, h2, h3⟩ := hball z hz
    have hzU : 0 < z.im := by linarith
    rw [Set.Finite.mem_toFinset]
    have hw : mob g z = ((g • (⟨z, hzU⟩ : ℍ) : ℍ) : ℂ) := by
      rw [mob, UpperHalfPlane.ofComplex_apply_of_im_pos hzU]
    rw [hw] at hg
    exact ⟨⟨z, hzU⟩, h1, h2, h3, hg⟩

/-! ### The cutoff -/

variable (Γ : Subgroup SL(2, ℤ)) (R : Finset SL(2, ℤ))

/-- Every subgroup of finite index has a finite set of left coset representatives. -/
theorem exists_cosetReps [Γ.FiniteIndex] :
    ∃ R : Finset SL(2, ℤ), ∀ g : SL(2, ℤ), ∃ r ∈ R, ∃ γ ∈ Γ, g = r * γ := by
  have := Subgroup.finite_quotient_of_finiteIndex (H := Γ)
  refine ⟨(Set.finite_range fun q : SL(2, ℤ) ⧸ Γ => q.out).toFinset, fun g => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Γ g
  refine ⟨(g : SL(2, ℤ) ⧸ Γ).out, (Set.Finite.mem_toFinset _).mpr (Set.mem_range_self _),
    (h : SL(2, ℤ))⁻¹, Γ.inv_mem h.2, ?_⟩
  rw [hh]
  group

/-- The seed `∑_{r ∈ R} bump (r z)`. -/
def seed (z : ℂ) : ℝ := ∑ r ∈ R, bump (mob r z)

/-- The `Γ`-periodization `∑ᶠ_{γ ∈ Γ} seed (γ⁻¹ z)`. -/
def mass (z : ℂ) : ℝ := ∑ᶠ γ : Γ, seed R (mob (γ : SL(2, ℤ))⁻¹ z)

/-- The cutoff `seed / mass`. -/
def cutoff (z : ℂ) : ℝ := seed R z / mass Γ R z

theorem seed_nonneg (z : ℂ) : 0 ≤ seed R z := Finset.sum_nonneg fun _ _ => bump_nonneg _

theorem contDiffOn_seed : ContDiffOn ℝ ∞ (seed R) U :=
  ContDiffOn.sum fun r _ => contDiff_bump.comp_contDiffOn (contDiffOn_mob r)

theorem mem_siegel_of_seed_ne_zero {z : ℂ} (h : seed R z ≠ 0) :
    ∃ r ∈ R, |(mob r z).re| ≤ 1 ∧ 1 / 2 ≤ (mob r z).im := by
  obtain ⟨r, hr, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨r, hr, mem_of_bump_ne_zero hne⟩

/-- Local finiteness of the `Γ`-translates of the seed. -/
theorem exists_finite_nbhd_seed {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧ ∃ T : Finset Γ, ∀ z ∈ V, ∀ γ : Γ,
      seed R (mob (γ : SL(2, ℤ))⁻¹ z) ≠ 0 → γ ∈ T := by
  classical
  obtain ⟨V, hVo, hzV, hVU, T₀, hT₀⟩ := exists_finite_nbhd hz₀
  refine ⟨V, hVo, hzV, hVU,
    ((T₀ ×ˢ R).image fun p : SL(2, ℤ) × SL(2, ℤ) => p.1⁻¹ * p.2).subtype (· ∈ Γ), ?_⟩
  intro z hz γ hγ
  obtain ⟨r, hr, hmem⟩ := mem_siegel_of_seed_ne_zero R hγ
  rw [← mob_mul] at hmem
  have ht := hT₀ z hz _ hmem
  rw [Finset.mem_subtype, Finset.mem_image]
  exact ⟨(r * (γ : SL(2, ℤ))⁻¹, r), Finset.mem_product.mpr ⟨ht, hr⟩, by group⟩

theorem hasFiniteSupport_seed {z : ℂ} (hz : z ∈ U) :
    Function.HasFiniteSupport fun γ : Γ => seed R (mob (γ : SL(2, ℤ))⁻¹ z) := by
  obtain ⟨V, -, hzV, -, T, hT⟩ := exists_finite_nbhd_seed Γ R hz
  exact T.finite_toSet.subset fun γ hγ => hT z hzV γ hγ

theorem mass_eq_sum {V : Set ℂ} {T : Finset Γ}
    (hT : ∀ z ∈ V, ∀ γ : Γ, seed R (mob (γ : SL(2, ℤ))⁻¹ z) ≠ 0 → γ ∈ T) {z : ℂ} (hz : z ∈ V) :
    mass Γ R z = ∑ γ ∈ T, seed R (mob (γ : SL(2, ℤ))⁻¹ z) :=
  finsum_eq_sum_of_support_subset _ fun γ hγ => hT z hz γ hγ

theorem contDiffOn_mass : ContDiffOn ℝ ∞ (mass Γ R) U := by
  refine contDiffOn_of_locally_contDiffOn fun z₀ hz₀ => ?_
  obtain ⟨V, hVo, hzV, -, T, hT⟩ := exists_finite_nbhd_seed Γ R hz₀
  refine ⟨V, hVo, hzV, ?_⟩
  have h : ContDiffOn ℝ ∞ (fun z => ∑ γ ∈ T, seed R (mob (γ : SL(2, ℤ))⁻¹ z)) (U ∩ V) :=
    ContDiffOn.sum fun γ _ =>
      ((contDiffOn_seed R).comp (contDiffOn_mob _) (mapsTo_mob _)).mono Set.inter_subset_left
  exact h.congr fun z hz => mass_eq_sum Γ R hT hz.2

theorem mass_mob (δ : Γ) (z : ℂ) : mass Γ R (mob δ z) = mass Γ R z := by
  unfold mass
  rw [← finsum_comp_equiv (Equiv.mulLeft δ)
    (f := fun γ : Γ => seed R (mob (γ : SL(2, ℤ))⁻¹ (mob δ z)))]
  refine finsum_congr fun γ => ?_
  rw [Equiv.coe_mulLeft, ← mob_mul, Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]

/-- The covering hypothesis: every `g` is `r γ` with `r ∈ R`, `γ ∈ Γ`. -/
def IsCover : Prop := ∀ g : SL(2, ℤ), ∃ r ∈ R, ∃ γ ∈ Γ, g = r * γ

theorem mass_pos (hR : IsCover Γ R) {z : ℂ} (hz : z ∈ U) : 0 < mass Γ R z := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd (⟨z, hz⟩ : ℍ)
  obtain ⟨r, hr, γ, hγ, rfl⟩ := hR g
  have hpos : 0 < bump (mob r (mob γ z)) := by
    have hw : mob (r * γ) z = (((r * γ) • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := by
      rw [mob, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    rw [← mob_mul, hw]
    exact bump_pos_of_mem_fd hg
  have h1 : bump (mob r (mob γ z)) ≤ seed R (mob γ z) :=
    Finset.single_le_sum (f := fun r => bump (mob r (mob γ z))) (fun r _ => bump_nonneg _) hr
  have h2 : seed R (mob γ z) ≤ mass Γ R z := by
    have := single_le_finsum ((⟨γ, hγ⟩ : Γ)⁻¹) (hasFiniteSupport_seed Γ R hz)
      fun γ => seed_nonneg R _
    simpa [mass] using this
  linarith

theorem cutoff_nonneg (z : ℂ) : 0 ≤ cutoff Γ R z := by
  rw [cutoff]
  exact div_nonneg (seed_nonneg R z)
    (finsum_nonneg fun γ => seed_nonneg R _)

theorem contDiffOn_cutoff (hR : IsCover Γ R) : ContDiffOn ℝ ∞ (cutoff Γ R) U :=
  (contDiffOn_seed R).div (contDiffOn_mass Γ R) fun _ hz => (mass_pos Γ R hR hz).ne'

theorem seed_ne_zero_of_cutoff_ne_zero {z : ℂ} (h : cutoff Γ R z ≠ 0) : seed R z ≠ 0 := by
  intro h0
  apply h
  rw [cutoff, h0, zero_div]

/-- The support of the cutoff lies in the finitely many translates `r⁻¹ S`, `r ∈ R`. -/
theorem mem_siegel_of_cutoff_ne_zero {z : ℂ} (h : cutoff Γ R z ≠ 0) :
    ∃ r ∈ R, |(mob r z).re| ≤ 1 ∧ 1 / 2 ≤ (mob r z).im :=
  mem_siegel_of_seed_ne_zero R (seed_ne_zero_of_cutoff_ne_zero Γ R h)

/-- Local finiteness of the `Γ`-translates of the cutoff. -/
theorem exists_finite_nbhd_cutoff {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧ ∃ T : Finset Γ, ∀ z ∈ V, ∀ γ : Γ,
      cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) ≠ 0 → γ ∈ T := by
  obtain ⟨V, hVo, hzV, hVU, T, hT⟩ := exists_finite_nbhd_seed Γ R hz₀
  exact ⟨V, hVo, hzV, hVU, T, fun z hz γ hγ =>
    hT z hz γ (seed_ne_zero_of_cutoff_ne_zero Γ R hγ)⟩

theorem hasFiniteSupport_cutoff {z : ℂ} (hz : z ∈ U) :
    Function.HasFiniteSupport fun γ : Γ => cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) := by
  obtain ⟨V, -, hzV, -, T, hT⟩ := exists_finite_nbhd_cutoff Γ R hz
  exact T.finite_toSet.subset fun γ hγ => hT z hzV γ hγ

/-- The `Γ`-translates of the cutoff sum to one on `U`. -/
theorem finsum_cutoff (hR : IsCover Γ R) {z : ℂ} (hz : z ∈ U) :
    ∑ᶠ γ : Γ, cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) = 1 := by
  have h : ∀ γ : Γ, cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) =
      seed R (mob (γ : SL(2, ℤ))⁻¹ z) * (mass Γ R z)⁻¹ := by
    intro γ
    rw [cutoff, div_eq_mul_inv]
    congr 2
    rw [← Subgroup.coe_inv]
    exact mass_mob Γ R γ⁻¹ z
  simp_rw [h]
  rw [← finsum_mul]
  exact mul_inv_cancel₀ (mass_pos Γ R hR hz).ne'

/-- Only finitely many `Γ`-translates of the cutoff meet a compact subset of `U`. -/
theorem finite_translates_of_isCompact {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    {γ : Γ | ∃ z ∈ K, cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) ≠ 0}.Finite := by
  have hloc : ∀ z ∈ U, ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ ∃ T : Finset Γ, ∀ w ∈ V, ∀ γ : Γ,
      cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ w) ≠ 0 → γ ∈ T := by
    intro z hz
    obtain ⟨V, hVo, hzV, -, T, hT⟩ := exists_finite_nbhd_cutoff Γ R hz
    exact ⟨V, hVo, hzV, T, hT⟩
  choose! V hVo hzV T hT using hloc
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover V fun z hz =>
    (hVo z (hKU hz)).mem_nhds (hzV z (hKU hz))
  refine (Set.Finite.biUnion t.finite_toSet fun x _ => (T x).finite_toSet).subset ?_
  rintro γ ⟨z, hz, hne⟩
  obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (hcov hz)
  exact Set.mem_iUnion₂.mpr ⟨x, hx, hT x (hKU (htK x hx)) z hzx γ hne⟩

/-! ### The equivariant primitive -/

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The primitive `∑ᶠ_{γ ∈ Γ} cutoff (γ⁻¹ z) • c γ` of a cochain `c`. -/
def primitive (c : Γ → W) (z : ℂ) : W :=
  ∑ᶠ γ : Γ, cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) • c γ

theorem contDiffOn_primitive (hR : IsCover Γ R) (c : Γ → W) :
    ContDiffOn ℝ ∞ (primitive Γ R c) U := by
  refine contDiffOn_of_locally_contDiffOn fun z₀ hz₀ => ?_
  obtain ⟨V, hVo, hzV, -, T, hT⟩ := exists_finite_nbhd_cutoff Γ R hz₀
  refine ⟨V, hVo, hzV, ?_⟩
  have h : ContDiffOn ℝ ∞
      (fun z => ∑ γ ∈ T, cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) • c γ) (U ∩ V) :=
    ContDiffOn.sum fun γ _ =>
      ((((contDiffOn_cutoff Γ R hR).comp (contDiffOn_mob _) (mapsTo_mob _)).smul
        contDiffOn_const).mono Set.inter_subset_left)
  exact h.congr fun z hz => finsum_eq_sum_of_support_subset _ fun γ hγ => hT z hz.2 γ
    (Function.support_smul_subset_left (fun γ : Γ => cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z))
      (fun γ => c γ) hγ)

/-- The primitive of a `1`-cocycle is equivariant: `φ (δ z) = ρ δ (φ z) + c δ`. -/
theorem primitive_mob (hR : IsCover Γ R) (ρ : Γ → W →ₗ[ℝ] W) (c : Γ → W)
    (hc : ∀ δ γ : Γ, c (δ * γ) = c δ + ρ δ (c γ)) (δ : Γ) {z : ℂ} (hz : z ∈ U) :
    primitive Γ R c (mob δ z) = ρ δ (primitive Γ R c z) + c δ := by
  have hfa := hasFiniteSupport_cutoff Γ R hz
  have hshift : ∀ γ : Γ, cutoff Γ R (mob ((δ * γ : Γ) : SL(2, ℤ))⁻¹ (mob δ z)) =
      cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) := by
    intro γ
    rw [← mob_mul, Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]
  have hf1 : Function.HasFiniteSupport
      fun γ : Γ => cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) • c δ :=
    hfa.subset (Function.support_smul_subset_left _ _)
  have hf2 : Function.HasFiniteSupport
      fun γ : Γ => cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) • ρ δ (c γ) :=
    hfa.subset (Function.support_smul_subset_left _ _)
  have hf3 : Function.HasFiniteSupport
      fun γ : Γ => cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ z) • c γ :=
    hfa.subset (Function.support_smul_subset_left _ _)
  unfold primitive
  rw [← finsum_comp_equiv (Equiv.mulLeft δ)
    (f := fun γ : Γ => cutoff Γ R (mob (γ : SL(2, ℤ))⁻¹ (mob δ z)) • c γ)]
  simp only [Equiv.coe_mulLeft, hshift, hc, smul_add]
  rw [finsum_add_distrib hf1 hf2, ← finsum_smul, finsum_cutoff Γ R hR hz, one_smul, add_comm,
    map_finsum (ρ δ) hf3]
  simp only [map_smul]

/-- Equivariant primitives exist for every `1`-cocycle of a finite-index subgroup. -/
theorem exists_equivariant_primitive [Γ.FiniteIndex] (ρ : Γ → W →ₗ[ℝ] W) (c : Γ → W)
    (hc : ∀ δ γ : Γ, c (δ * γ) = c δ + ρ δ (c γ)) :
    ∃ φ : ℂ → W, ContDiffOn ℝ ∞ φ U ∧ ∀ δ : Γ, ∀ z ∈ U, φ (mob δ z) = ρ δ (φ z) + c δ := by
  obtain ⟨R, hR⟩ := exists_cosetReps Γ
  exact ⟨primitive Γ R c, contDiffOn_primitive Γ R hR c,
    fun δ z hz => primitive_mob Γ R hR ρ c hc δ hz⟩

/-- The matrix form: `ρ δ` acting on `EuclideanSpace ℂ (Fin d)` through `Matrix.toEuclideanLin`. -/
theorem exists_equivariant_primitive_matrix {d : ℕ} [Γ.FiniteIndex]
    (ρ : Γ → Matrix (Fin d) (Fin d) ℂ) (c : Γ → EuclideanSpace ℂ (Fin d))
    (hc : ∀ δ γ : Γ, c (δ * γ) = c δ + Matrix.toEuclideanLin (ρ δ) (c γ)) :
    ∃ φ : ℂ → EuclideanSpace ℂ (Fin d), ContDiffOn ℝ ∞ φ U ∧
      ∀ δ : Γ, ∀ z ∈ U, φ (mob δ z) = Matrix.toEuclideanLin (ρ δ) (φ z) + c δ :=
  exists_equivariant_primitive Γ (fun δ => (Matrix.toEuclideanLin (ρ δ)).restrictScalars ℝ) c hc

end TernaryPeriodPolynomials.Argument.ESFoundations.Partition
