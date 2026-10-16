module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.PeterssonHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneMultiplicityOne

@[expose] public section


/-!
# Semisimplicity of the level-one Hecke operators

The Petersson product `pet` is a positive definite Hermitian form on level-one cusp forms
(`pet_self_eq_zero`), for which every `T_p` is self-adjoint (`PeterssonHecke.pet_hecke`). A
self-adjoint operator for a positive definite Hermitian form has no nilpotent part
(`ker_sq_le_ker`, an abstract lemma), so generalized eigenvectors of `T_p` are eigenvectors
(`maxGenEigenspace_le_eigenspace`). With multiplicity one away from three, the joint generalized
eigenspace of `{T_p : p ≠ 3}` for any system of eigenvalues has dimension at most one
(`finrank_jointGenEigenspaceAwayThree_le_one`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open UpperHalfPlane Matrix MeasureTheory ComplexConjugate
open scoped MatrixGroups Pointwise ModularForm Manifold

namespace TernaryPeriodPolynomials.Spectral.PeterssonSemisimple

open PeterssonDomain PeterssonHecke LevelOneHecke LevelOneMultiplicityOne

/-! ### An abstract lemma: self-adjoint operators have no nilpotent part -/

section Abstract

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (B : V → V → ℂ)
  (sub_left : ∀ x y z, B (x - y) z = B x z - B y z)
  (smul_left : ∀ (a : ℂ) x z, B (a • x) z = conj a * B x z)
  (sub_right : ∀ x y z, B z (x - y) = B z x - B z y)
  (smul_right : ∀ (a : ℂ) x z, B z (a • x) = a * B z x)
  (definite : ∀ x, B x x = 0 → x = 0)
  (T : Module.End ℂ V) (selfAdjoint : ∀ x y, B (T x) y = B x (T y))

include sub_left smul_left sub_right smul_right selfAdjoint in
theorem shift_adjoint (μ : ℂ) (x y : V) :
    B ((T - μ • 1) x) y = B x ((T - conj μ • 1) y) := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [sub_left, smul_left, sub_right, smul_right, selfAdjoint]

include sub_left smul_left sub_right smul_right definite selfAdjoint in
/-- **No Jordan blocks.** -/
theorem ker_sq_le_ker (μ : ℂ) (v : V) (hv : (T - μ • 1) ((T - μ • 1) v) = 0) :
    (T - μ • 1) v = 0 := by
  set N : Module.End ℂ V := T - μ • 1
  set N' : Module.End ℂ V := T - conj μ • 1
  have hcomm : N * N' = N' * N := by
    have : Commute N N' :=
      ((Commute.refl T).sub_right ((Commute.one_right T).smul_right _)).sub_left
        (((Commute.one_left T).smul_left _).sub_right
          ((Commute.one_left _).smul_left _ |>.smul_right _))
    exact this.eq
  have hadj : ∀ x y, B (N x) y = B x (N' y) := shift_adjoint B sub_left smul_left sub_right
    smul_right T selfAdjoint μ
  have hadj' : ∀ x y, B (N' x) y = B x (N y) := by
    intro x y
    have := shift_adjoint B sub_left smul_left sub_right smul_right T selfAdjoint (conj μ) x y
    rwa [Complex.conj_conj] at this
  have hzero : ∀ z, B z 0 = 0 := by
    intro z
    have := smul_right 0 0 z
    rwa [zero_smul, zero_mul] at this
  have hN'w : N' (N v) = 0 := by
    apply definite
    rw [hadj', ← Module.End.mul_apply, hcomm, Module.End.mul_apply, hv, map_zero, hzero]
  apply definite
  rw [hadj, hN'w, hzero]

include sub_left smul_left sub_right smul_right definite selfAdjoint in
theorem pow_ker_le_ker (μ : ℂ) : ∀ (n : ℕ) (v : V), ((T - μ • 1) ^ n) v = 0 → (T - μ • 1) v = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    match n, ih, hv with
    | 0, _, hv =>
      rw [pow_zero, Module.End.one_apply] at hv
      rw [hv, map_zero]
    | 1, _, hv => rwa [pow_one] at hv
    | m + 2, ih, hv =>
      have h2 : (T - μ • 1) ((T - μ • 1) (((T - μ • 1) ^ m) v)) = 0 := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← sq, ← pow_add, add_comm]
        exact hv
      have h1 := ker_sq_le_ker B sub_left smul_left sub_right smul_right definite T selfAdjoint μ _ h2
      apply ih (m + 1) (by omega)
      rw [pow_succ', Module.End.mul_apply]
      exact h1

include sub_left smul_left sub_right smul_right definite selfAdjoint in
theorem maxGenEigenspace_le_eigenspace_abstract (μ : ℂ) :
    T.maxGenEigenspace μ ≤ T.eigenspace μ := by
  intro v hv
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨n, hn⟩ := hv
  have h := pow_ker_le_ker B sub_left smul_left sub_right smul_right definite T selfAdjoint μ n v hn
  rw [Module.End.mem_eigenspace_iff]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  exact h

end Abstract

/-! ### The Petersson product is a positive definite Hermitian form -/

variable (k : ℤ)

theorem integrableOn_petersson (f g : CuspForm levelOne k) :
    IntegrableOn (petersson k f g) ModularGroup.fd volume :=
  integrableOn_fd (petersson_continuous k (continuous_cuspForm k f) (continuous_cuspForm k g))
    (bounded_petersson k (pbounded_cuspForm k f) (pbounded_cuspForm k g))

theorem pet_sub_left (f g h : CuspForm levelOne k) : pet k (f - g) h = pet k f h - pet k g h := by
  unfold pet
  rw [← integral_sub (integrableOn_petersson k f h) (integrableOn_petersson k g h)]
  congr 1
  funext τ
  simp only [petersson, FunLike.coe_sub, Pi.sub_apply, map_sub]
  ring

theorem pet_sub_right (f g h : CuspForm levelOne k) : pet k h (f - g) = pet k h f - pet k h g := by
  unfold pet
  rw [← integral_sub (integrableOn_petersson k h f) (integrableOn_petersson k h g)]
  congr 1
  funext τ
  simp only [petersson, FunLike.coe_sub, Pi.sub_apply]
  ring

theorem pet_smul_left (a : ℂ) (f h : CuspForm levelOne k) : pet k (a • f) h = conj a * pet k f h := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  simp only [petersson, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem pet_smul_right (a : ℂ) (f h : CuspForm levelOne k) : pet k h (a • f) = a * pet k h f := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  simp only [petersson, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem volume_open_pos {U : Set ℍ} (hU : IsOpen U) (hne : U.Nonempty) : 0 < volume U := by
  rw [volume_eq_lintegral]
  have hopen : IsOpen (UpperHalfPlane.coe '' U) := isOpenEmbedding_coe.isOpenMap U hU
  have hpos : 0 < volume (UpperHalfPlane.coe '' U) := hopen.measure_pos volume (hne.image _)
  rw [setLIntegral_pos_iff (by fun_prop)]
  convert hpos using 2
  ext z
  simp only [Set.mem_inter_iff, Function.mem_support, and_iff_right_iff_imp]
  rintro ⟨τ, -, rfl⟩
  have him : 0 < (τ : ℂ).im := τ.im_pos
  have : (1 / ‖(τ : ℂ).im‖₊ : NNReal) ≠ 0 := by
    rw [one_div, ne_eq, inv_eq_zero, nnnorm_eq_zero]
    exact him.ne'
  exact_mod_cast pow_ne_zero 2 this

/-- The density `|f|² y^k` of `pet f f`. -/
def selfDensity (f : CuspForm levelOne k) (τ : ℍ) : ℝ := ‖f τ‖ ^ 2 * τ.im ^ k

theorem petersson_self (f : CuspForm levelOne k) (τ : ℍ) :
    petersson k f f τ = (selfDensity k f τ : ℂ) := by
  simp only [petersson, selfDensity, Complex.conj_mul', Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_zpow]

theorem selfDensity_nonneg (f : CuspForm levelOne k) (τ : ℍ) : 0 ≤ selfDensity k f τ :=
  mul_nonneg (sq_nonneg _) (zpow_nonneg τ.im_pos.le _)

theorem continuous_selfDensity (f : CuspForm levelOne k) : Continuous (selfDensity k f) := by
  unfold selfDensity
  have h1 : Continuous fun τ : ℍ => ‖f τ‖ ^ 2 := ((continuous_cuspForm k f).norm).pow 2
  have h2 : Continuous fun τ : ℍ => τ.im ^ k :=
    UpperHalfPlane.continuous_im.zpow₀ k fun τ => Or.inl τ.im_pos.ne'
  exact h1.mul h2

/-- A holomorphic function on `ℍ` vanishing on the interior of `𝒟` vanishes. -/
theorem eq_zero_of_eqOn_fdo (f : CuspForm levelOne k) (h : ∀ τ ∈ ModularGroup.fdo, f τ = 0) :
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

/-- **Positive definiteness** of the Petersson product. -/
theorem pet_self_eq_zero (f : CuspForm levelOne k) (h : pet k f f = 0) : f = 0 := by
  unfold pet at h
  simp_rw [petersson_self] at h
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h
  have hint : IntegrableOn (selfDensity k f) ModularGroup.fd volume := by
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
    have hnull : (volume.restrict ModularGroup.fd) {τ | selfDensity k f τ ≠ 0} = 0 := by
      rw [Filter.EventuallyEq, ae_iff] at hae
      simpa only [Pi.zero_apply] using hae
    rw [Measure.restrict_apply' ModularGroup.isClosed_fd.measurableSet] at hnull
    have hsub : U ⊆ {τ | selfDensity k f τ ≠ 0} ∩ ModularGroup.fd :=
      fun τ hτ => ⟨hτ.2, ModularGroup.fdo_subset_fd hτ.1⟩
    exact absurd (measure_mono_null hsub hnull) hUpos.ne'
  apply eq_zero_of_eqOn_fdo k f
  intro τ hτ
  have h0 := hfdo τ hτ
  unfold selfDensity at h0
  have hy : τ.im ^ k ≠ 0 := zpow_ne_zero _ τ.im_pos.ne'
  have : ‖f τ‖ ^ 2 = 0 := (mul_eq_zero.mp h0).resolve_right hy
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

/-! ### Consequences -/

/-- **Generalized eigenvectors of `T_p` are eigenvectors.** -/
theorem maxGenEigenspace_le_eigenspace (p : Nat.Primes) (μ : ℂ) :
    Module.End.maxGenEigenspace (levelOneHecke k p) μ ≤ Module.End.eigenspace (levelOneHecke k p) μ :=
  maxGenEigenspace_le_eigenspace_abstract (pet k) (pet_sub_left k) (pet_smul_left k)
    (pet_sub_right k) (pet_smul_right k) (pet_self_eq_zero k) (levelOneHecke k p) (pet_hecke k p) μ

/-- The joint generalized eigenspace of the `T_p`, `p ≠ 3`. -/
def jointGenEigenspaceAwayThree (eigenvalues : Nat.Primes → ℂ) : Submodule ℂ (CuspForm levelOne k) :=
  ⨅ p : {p : Nat.Primes // p.val ≠ 3}, Module.End.maxGenEigenspace (levelOneHecke k p.1) (eigenvalues p.1)

theorem jointGenEigenspaceAwayThree_le (eigenvalues : Nat.Primes → ℂ) :
    jointGenEigenspaceAwayThree k eigenvalues ≤ eigenspaceAwayThree k eigenvalues :=
  iInf_mono fun p => maxGenEigenspace_le_eigenspace k p.1 _

/-- **Generalized multiplicity one away from three at level one.** -/
theorem finrank_jointGenEigenspaceAwayThree_le_one [FiniteDimensional ℂ (CuspForm levelOne k)]
    (hk : 0 < k) (eigenvalues : Nat.Primes → ℂ) :
    Module.finrank ℂ (jointGenEigenspaceAwayThree k eigenvalues) ≤ 1 :=
  (Submodule.finrank_mono (jointGenEigenspaceAwayThree_le k eigenvalues)).trans
    (finrank_eigenspaceAwayThree_le_one hk eigenvalues)

end TernaryPeriodPolynomials.Spectral.PeterssonSemisimple
