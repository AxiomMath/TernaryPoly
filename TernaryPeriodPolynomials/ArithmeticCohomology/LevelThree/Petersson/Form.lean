module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Petersson.Domain
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Petersson.Adjoint
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeSum
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.PeterssonSemisimple

@[expose] public section


/-!
# The Petersson product on `S_k(Γ₁(3))`

`petThree k f g = ∫_{𝒟₃} conj(f) g y^k dμ` over the fundamental domain `fdThree` of `Γ₁(3)`.
It is a sesquilinear form (`petThree_sub_left`, `petThree_smul_left`, ...) and positive definite
(`petThree_self_eq_zero`): the density `|f|² y^k` is continuous and nonnegative, the standard
fundamental domain `𝒟 ⊆ 𝒟₃` has nonempty interior, and a cusp form vanishing on an open set
vanishes by the identity theorem. Integrability comes from the boundedness of Petersson products
of cusp forms (Mathlib) and the finiteness of `vol(𝒟₃)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open UpperHalfPlane Matrix MeasureTheory ComplexConjugate
open scoped MatrixGroups Pointwise ModularForm Manifold

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonForm

open TernaryPeriodPolynomials.Spectral.PeterssonDomain
open TernaryPeriodPolynomials.Spectral.PeterssonHecke
open TernaryPeriodPolynomials.Spectral.PeterssonSemisimple (volume_open_pos)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonDomain
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeSum

variable (k : ℤ)

theorem pbounded_cuspForm (f : CuspForm levelThree k) : PBounded k f :=
  CuspFormClass.petersson_bounded_left k levelThree f f

theorem continuous_cuspForm (f : CuspForm levelThree k) : Continuous (f : ℍ → ℂ) :=
  f.holo'.continuous

theorem continuous_slash_cuspForm (f : CuspForm levelThree k) (g : GL (Fin 2) ℝ) :
    Continuous ((f : ℍ → ℂ) ∣[k] g) :=
  (CuspForm.translate f g).holo'.continuous

theorem integrableOn_fdThree {Φ : ℍ → ℂ} (hc : Continuous Φ) (hb : ∃ C, ∀ τ, ‖Φ τ‖ ≤ C) :
    IntegrableOn Φ fdThree volume := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ hC)

theorem integrableOn_petersson (f g : CuspForm levelThree k) :
    IntegrableOn (petersson k f g) fdThree volume :=
  integrableOn_fdThree
    (petersson_continuous k (continuous_cuspForm k f) (continuous_cuspForm k g))
    (bounded_petersson k (pbounded_cuspForm k f) (pbounded_cuspForm k g))

/-- **The Petersson product** `∫_{𝒟₃} conj(f) g y^k dμ` on `S_k(Γ₁(3))`. -/
def petThree (f g : CuspForm levelThree k) : ℂ := ∫ τ in fdThree, petersson k f g τ

theorem petThree_sub_left (f g h : CuspForm levelThree k) :
    petThree k (f - g) h = petThree k f h - petThree k g h := by
  unfold petThree
  rw [← integral_sub (integrableOn_petersson k f h) (integrableOn_petersson k g h)]
  congr 1
  funext τ
  simp only [petersson, FunLike.coe_sub, Pi.sub_apply, map_sub]
  ring

theorem petThree_sub_right (f g h : CuspForm levelThree k) :
    petThree k h (f - g) = petThree k h f - petThree k h g := by
  unfold petThree
  rw [← integral_sub (integrableOn_petersson k h f) (integrableOn_petersson k h g)]
  congr 1
  funext τ
  simp only [petersson, FunLike.coe_sub, Pi.sub_apply]
  ring

theorem petThree_smul_left (a : ℂ) (f h : CuspForm levelThree k) :
    petThree k (a • f) h = conj a * petThree k f h := by
  unfold petThree
  rw [← integral_const_mul]
  congr 1
  funext τ
  simp only [petersson, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem petThree_smul_right (a : ℂ) (f h : CuspForm levelThree k) :
    petThree k h (a • f) = a * petThree k h f := by
  unfold petThree
  rw [← integral_const_mul]
  congr 1
  funext τ
  simp only [petersson, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The density `|f|² y^k` of `petThree f f`. -/
def selfDensity (f : CuspForm levelThree k) (τ : ℍ) : ℝ := ‖f τ‖ ^ 2 * τ.im ^ k

theorem petersson_self (f : CuspForm levelThree k) (τ : ℍ) :
    petersson k f f τ = (selfDensity k f τ : ℂ) := by
  simp only [petersson, selfDensity, Complex.conj_mul', Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_zpow]

theorem selfDensity_nonneg (f : CuspForm levelThree k) (τ : ℍ) : 0 ≤ selfDensity k f τ :=
  mul_nonneg (sq_nonneg _) (zpow_nonneg τ.im_pos.le _)

theorem continuous_selfDensity (f : CuspForm levelThree k) : Continuous (selfDensity k f) := by
  unfold selfDensity
  have h1 : Continuous fun τ : ℍ => ‖f τ‖ ^ 2 := ((continuous_cuspForm k f).norm).pow 2
  have h2 : Continuous fun τ : ℍ => τ.im ^ k :=
    UpperHalfPlane.continuous_im.zpow₀ k fun τ => Or.inl τ.im_pos.ne'
  exact h1.mul h2

/-- A holomorphic function on `ℍ` vanishing on the interior of `𝒟` vanishes. -/
theorem eq_zero_of_eqOn_fdo (f : CuspForm levelThree k) (h : ∀ τ ∈ ModularGroup.fdo, f τ = 0) :
    f = 0 := by
  have hdiff := (UpperHalfPlane.mdifferentiable_iff).mp f.holo'
  have hana := hdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_im)
  have hconn : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hz₀ : ((twoI : ℍ) : ℂ) ∈ {z : ℂ | 0 < z.im} := twoI.im_pos
  have hev : (⇑f ∘ ↑ofComplex) =ᶠ[nhds ((twoI : ℍ) : ℂ)] 0 := by
    have hopen : IsOpen (UpperHalfPlane.coe '' ModularGroup.fdo) :=
      isOpenEmbedding_coe.isOpenMap _ ModularGroup.isOpen_fdo
    filter_upwards [hopen.mem_nhds ⟨twoI, twoI_mem_fdo, rfl⟩] with z hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    simp only [Function.comp_apply, ofComplex_apply, Pi.zero_apply]
    exact h τ hτ
  have heq := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀ hev
  ext τ
  have := heq τ.im_pos
  simp only [Function.comp_apply, ofComplex_apply, Pi.zero_apply] at this
  exact this

/-- **Positive definiteness** of the Petersson product on `S_k(Γ₁(3))`. -/
theorem petThree_self_eq_zero (f : CuspForm levelThree k) (h : petThree k f f = 0) : f = 0 := by
  unfold petThree at h
  simp_rw [petersson_self] at h
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h
  have hint : IntegrableOn (selfDensity k f) fdThree volume := by
    refine (integrableOn_petersson k f f).norm.congr (ae_of_all _ fun τ => ?_)
    change ‖petersson k f f τ‖ = selfDensity k f τ
    rw [petersson_self, Complex.norm_real, Real.norm_of_nonneg (selfDensity_nonneg k f τ)]
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ fun τ => selfDensity_nonneg k f τ) hint).mp h
  have hfdo : ∀ τ ∈ ModularGroup.fdo, selfDensity k f τ = 0 := by
    intro τ₀ hτ₀
    by_contra hne
    let U := ModularGroup.fdo ∩ {τ | selfDensity k f τ ≠ 0}
    have hUopen : IsOpen U :=
      ModularGroup.isOpen_fdo.inter (isOpen_ne_fun (continuous_selfDensity k f) continuous_const)
    have hUpos := volume_open_pos hUopen ⟨τ₀, hτ₀, hne⟩
    have hnull : (volume.restrict fdThree) {τ | selfDensity k f τ ≠ 0} = 0 := by
      rw [Filter.EventuallyEq, ae_iff] at hae
      simpa only [Pi.zero_apply] using hae
    rw [Measure.restrict_apply₀' fdThree_isFundamentalDomain.nullMeasurableSet] at hnull
    have hsub : U ⊆ {τ | selfDensity k f τ ≠ 0} ∩ fdThree :=
      fun τ hτ => ⟨hτ.2, fd_subset_fdThree (ModularGroup.fdo_subset_fd hτ.1)⟩
    exact absurd (measure_mono_null hsub hnull) hUpos.ne'
  apply eq_zero_of_eqOn_fdo k f
  intro τ hτ
  have h0 := hfdo τ hτ
  unfold selfDensity at h0
  have hy : τ.im ^ k ≠ 0 := zpow_ne_zero _ τ.im_pos.ne'
  have : ‖f τ‖ ^ 2 = 0 := (mul_eq_zero.mp h0).resolve_right hy
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

end TernaryPeriodPolynomials.LevelThree.LevelThreePeterssonForm
