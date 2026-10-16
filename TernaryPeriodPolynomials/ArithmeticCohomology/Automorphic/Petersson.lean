module

public import Mathlib
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.RealHaar
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Unimodular
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.FundamentalDomain
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.ProductHaar
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.AdelicReduction
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ArithmeticModularity
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Norm
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.NormContinuity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.RationalNorm
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Norm
public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.Space

@[expose] public section


/-!
# The Petersson pairing on `GL₂(ℚ)\GL₂(𝔸) / Z(ℝ)⁺`

Let `D` be the measurable fundamental domain of `GL₂(ℚ)` acting on `GL₂(𝔸)` by left
multiplication (`BinaryFundamentalDomain.domain`), and let `S = {x | 1 ≤ ‖det x‖_𝔸 < 2}` be the
shell of idelic determinant norm in `[1, 2)`.  `S` is invariant under `GL₂(ℚ)` (product formula)
and meets every `Z(ℝ)⁺`-orbit in a fundamental domain for the dilations, so for functions `φ, ψ`
that are left `GL₂(ℚ)`-invariant and have a common unitary central character the integral
`⟪φ, ψ⟫ = ∫_{D ∩ S} conj φ · ψ` is the Petersson pairing on `GL₂(ℚ) Z(ℝ)⁺ \ GL₂(𝔸)`.

Main results (all unconditional):

* `measure_domain_inter_shell_lt_top`: `D ∩ S` has finite Haar measure (finite covolume).  The
  proof covers `S` by `GL₂(ℚ)`-translates of the set `Σ × GL₂(Ẑ)` where `Σ ⊆ GL₂(ℝ)` is the
  Siegel box (`measure_siegel_lt_top`, proved here for every left Haar measure on `GL₂(ℝ)`).
* `pet_right_invariant`: `⟪φ·g, ψ·g⟫ = ⟪φ, ψ⟫` for every `g ∈ GL₂(𝔸)`.
* `petCore`: `InnerProductSpace.Core ℂ (petSpace χ)` on the space of bounded continuous
  left-`GL₂(ℚ)`-invariant functions with unitary central character `χ`; the definiteness is
  `eq_zero_of_pet_self_eq_zero`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Set
open scoped ENNReal NNReal Pointwise
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Automorphic.RealHaar
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding

noncomputable section

namespace TernaryPeriodPolynomials.Automorphic.Petersson

/-! ## 1. Siegel boxes in `GL₂(ℝ)` have finite Haar measure -/

section Siegel

variable (μ : Measure BinaryRealGL) [μ.IsHaarMeasure]

theorem measure_strip_shift (α β t : ℝ) (I J : Set ℝ) :
    μ (strip α β ((· + t) ⁻¹' I) J) = μ (strip α β I J) := by
  rw [← preimage_unipotent_strip t α β I J]
  exact measure_preimage_mul μ (binaryUnipotent t) _

theorem measure_strip_scaling {s : ℝ} (hs : s ≠ 0) (α β : ℝ) (I J : Set ℝ) :
    μ (strip α β ((· / s ^ 2) ⁻¹' I) ((· / s ^ 2) ⁻¹' J)) = μ (strip α β I J) := by
  rw [← preimage_scaling_strip hs α β I J]
  exact measure_preimage_mul μ (scaling s hs) _

theorem strip_union (α β : ℝ) (I I' J : Set ℝ) :
    strip α β (I ∪ I') J = strip α β I J ∪ strip α β I' J := by
  ext g
  simp only [strip, Set.mem_ofPred_eq, Set.mem_union]
  tauto

theorem measure_strip_Ico_add (α β : ℝ) (J : Set ℝ) (u v t : ℝ) :
    μ (strip α β (Ico (u - t) (v - t)) J) = μ (strip α β (Ico u v) J) := by
  rw [← Set.preimage_add_const_Ico t u v]
  exact measure_strip_shift μ α β t _ J

/-- Halving the width of a band halves its measure. -/
theorem measure_strip_Ico_halve (α β : ℝ) {J : Set ℝ} (hJ : MeasurableSet J) (w : ℝ)
    (hw : 0 ≤ w) :
    μ (strip α β (Ico 0 w) J) = 2 * μ (strip α β (Ico 0 (w / 2)) J) := by
  have hunion : strip α β (Ico 0 w) J =
      strip α β (Ico 0 (w / 2)) J ∪ strip α β (Ico (w / 2) w) J := by
    rw [← strip_union, Set.Ico_union_Ico_eq_Ico (a := 0) (b := w / 2) (c := w)
      (by linarith) (by linarith)]
  have hdisj : Disjoint (strip α β (Ico 0 (w / 2)) J) (strip α β (Ico (w / 2) w) J) := by
    rw [Set.disjoint_left]
    intro g h1 h2
    obtain ⟨-, hr1, -⟩ := h1
    obtain ⟨-, hr2, -⟩ := h2
    exact absurd hr1.2 (not_lt.mpr hr2.1)
  have hmeas : MeasurableSet (strip α β (Ico (w / 2) w) J) :=
    measurableSet_strip α β measurableSet_Ico hJ
  have h := measure_strip_Ico_add μ α β J (w / 2) w (w / 2)
  rw [sub_self, show w - w / 2 = w / 2 by ring] at h
  calc μ (strip α β (Ico 0 w) J)
      = μ (strip α β (Ico 0 (w / 2)) J) + μ (strip α β (Ico (w / 2) w) J) := by
        rw [hunion]
        exact measure_union hdisj hmeas
    _ = μ (strip α β (Ico 0 (w / 2)) J) + μ (strip α β (Ico 0 (w / 2)) J) := by rw [h]
    _ = 2 * μ (strip α β (Ico 0 (w / 2)) J) := (two_mul _).symm

theorem measure_strip_Ico_pow (α β : ℝ) {J : Set ℝ} (hJ : MeasurableSet J) (w : ℝ)
    (hw : 0 ≤ w) (j : ℕ) :
    μ (strip α β (Ico 0 w) J) = 2 ^ j * μ (strip α β (Ico 0 (w / 2 ^ j)) J) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := measure_strip_Ico_halve μ α β hJ (w / 2 ^ j) (div_nonneg hw (by positivity))
    have e : w / 2 ^ j / 2 = w / 2 ^ (j + 1) := by rw [div_div, pow_succ]
    rw [e] at h
    rw [ih, h, ← mul_assoc, ← pow_succ]

/-- The `k`-th horizontal layer of the Siegel box. -/
def layer (α β c : ℝ) (k : ℕ) : Set BinaryRealGL :=
  strip α β (Ico (-1) 1) (Ico (c * 4 ^ k) (c * 4 ^ (k + 1)))

theorem siegel_subset_iUnion {α β c : ℝ} (hc : 0 < c) :
    strip α β (Ico (-1) 1) (Ici c) ⊆ ⋃ k : ℕ, layer α β c k := by
  intro g hg
  obtain ⟨hdet, hre, him⟩ := hg
  have him' : c ≤ orbitIm g := him
  have hx : 1 ≤ orbitIm g / c := by
    rw [le_div_iff₀ hc, one_mul]
    exact him'
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 4)
  refine Set.mem_iUnion.mpr ⟨k, hdet, hre, ?_, ?_⟩
  · rw [le_div_iff₀ hc] at hk1
    linarith
  · rw [div_lt_iff₀ hc] at hk2
    linarith

theorem preimage_div_Ico (s : ℝ) (hs : 0 < s) (u v : ℝ) :
    (fun x : ℝ => x / s) ⁻¹' Ico u v = Ico (u * s) (v * s) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Ico]
  rw [le_div_iff₀ hs, div_lt_iff₀ hs]

/-- Scaling by `diag(2⁻ᵏ, 2ᵏ)` identifies the `k`-th layer with a band of width `2 / 4ᵏ`. -/
theorem layer_mul (α β c : ℝ) (k : ℕ) :
    (4 : ℝ≥0∞) ^ k * μ (layer α β c k) = μ (strip α β (Ico 0 2) (Ico c (4 * c))) := by
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  have hs : (2 : ℝ) ^ k ≠ 0 := by positivity
  have h22 : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have e1 : (fun x : ℝ => x / 4 ^ k) ⁻¹' Ico (-((4 : ℝ) ^ k)⁻¹) (((4 : ℝ) ^ k)⁻¹) =
      Ico (-1) 1 := by
    rw [preimage_div_Ico _ h4, neg_mul, inv_mul_cancel₀ h4.ne']
  have e2 : (fun x : ℝ => x / 4 ^ k) ⁻¹' Ico c (4 * c) =
      Ico (c * 4 ^ k) (c * 4 ^ (k + 1)) := by
    have : 4 * c * (4 : ℝ) ^ k = c * 4 ^ (k + 1) := by ring
    rw [preimage_div_Ico _ h4, this]
  have hsc := measure_strip_scaling μ hs α β (Ico (-((4 : ℝ) ^ k)⁻¹) (((4 : ℝ) ^ k)⁻¹))
    (Ico c (4 * c))
  rw [h22, e1, e2] at hsc
  have hsh := measure_strip_Ico_add μ α β (Ico c (4 * c)) 0 (2 * ((4 : ℝ) ^ k)⁻¹)
    (((4 : ℝ) ^ k)⁻¹)
  rw [zero_sub, show 2 * ((4 : ℝ) ^ k)⁻¹ - ((4 : ℝ) ^ k)⁻¹ = ((4 : ℝ) ^ k)⁻¹ by ring] at hsh
  have hpow := measure_strip_Ico_pow μ α β (J := Ico c (4 * c)) measurableSet_Ico 2
    (by norm_num) (2 * k)
  have hw : (2 : ℝ) / 2 ^ (2 * k) = 2 * ((4 : ℝ) ^ k)⁻¹ := by
    rw [pow_mul, div_eq_mul_inv]
    norm_num
  have hE : (2 : ℝ≥0∞) ^ (2 * k) = 4 ^ k := by
    rw [pow_mul]
    norm_num
  rw [hw, ← hsh, ← hsc, hE] at hpow
  exact hpow.symm

/-- Finiteness of the Siegel box `{ det ∈ [α, β], Re ∈ [-1, 1), Im ≥ c }` for every left Haar
measure on `GL₂(ℝ)`. -/
theorem measure_siegel_lt_top {α β c : ℝ} (hα : 0 < α) (hc : 0 < c) :
    μ (strip α β (Ico (-1) 1) (Ici c)) < ⊤ := by
  have ha0 : μ (strip α β (Ico 0 2) (Ico c (4 * c))) < ⊤ := by
    have hcomp := isCompact_strip_Icc (β := β) hα hc 2 (4 * c)
    refine lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top
    intro g hg
    obtain ⟨hdet, hre, him⟩ := hg
    exact ⟨hdet, ⟨by linarith [hre.1], hre.2.le⟩, ⟨him.1, him.2.le⟩⟩
  have hk : ∀ k : ℕ, μ (layer α β c k) =
      ((4 : ℝ≥0∞)⁻¹) ^ k * μ (strip α β (Ico 0 2) (Ico c (4 * c))) := by
    intro k
    have h := layer_mul μ α β c k
    have h4 : (4 : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have h4' : (4 : ℝ≥0∞) ^ k ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
    rw [← ENNReal.inv_pow, ← h, ← mul_assoc, ENNReal.inv_mul_cancel h4 h4', one_mul]
  have hgeo : ∑' k : ℕ, ((4 : ℝ≥0∞)⁻¹) ^ k < ⊤ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_lt_top.mpr (tsub_pos_of_lt (ENNReal.inv_lt_one.mpr (by norm_num)))
  calc μ (strip α β (Ico (-1) 1) (Ici c)) ≤ μ (⋃ k : ℕ, layer α β c k) :=
        measure_mono (siegel_subset_iUnion hc)
    _ ≤ ∑' k : ℕ, μ (layer α β c k) := measure_iUnion_le _
    _ = (∑' k : ℕ, ((4 : ℝ≥0∞)⁻¹) ^ k) * μ (strip α β (Ico 0 2) (Ico c (4 * c))) := by
        simp_rw [hk]
        exact ENNReal.tsum_mul_right
    _ < ⊤ := ENNReal.mul_lt_top hgeo ha0

end Siegel

/-! ## 2. A cover bound for fundamental domains -/

section Cover

variable {Γ X : Type*} [Group Γ] [Countable Γ] [MulAction Γ X] [MeasurableSpace X]
  [MeasurableConstSMul Γ X] {μ : Measure X} [SMulInvariantMeasure Γ X μ]

/-- If `E` meets the orbit of every point of `S`, then `D ∩ S` is no bigger than `E`. -/
theorem measure_inter_le_of_cover {D E S : Set X} (hD : IsFundamentalDomain Γ D μ)
    (hcov : ∀ x ∈ S, ∃ γ : Γ, γ • x ∈ E) : μ (D ∩ S) ≤ μ E := by
  calc μ (D ∩ S) ≤ μ (⋃ γ : Γ, γ • E ∩ D) := by
        apply measure_mono
        rintro x ⟨hxD, hxS⟩
        obtain ⟨γ, hγ⟩ := hcov x hxS
        refine Set.mem_iUnion.mpr ⟨γ⁻¹, ?_, hxD⟩
        rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
        exact hγ
    _ ≤ ∑' γ : Γ, μ (γ • E ∩ D) := measure_iUnion_le _
    _ = μ E := (hD.measure_eq_tsum E).symm

end Cover

/-! ## 3. The idelic norm of the determinant and the shell -/

/-- The idelic norm `‖det x‖_𝔸` of an element of `GL₂(𝔸)`. -/
def detNorm (x : BinaryAdelicGL) : ℝ := (adeleNorm (GeneralLinearGroup.det x) : ℝ)

theorem detNorm_mul (x y : BinaryAdelicGL) : detNorm (x * y) = detNorm x * detNorm y := by
  simp only [detNorm, map_mul, NNReal.coe_mul]

theorem detNorm_pos (x : BinaryAdelicGL) : 0 < detNorm x :=
  NNReal.coe_pos.mpr (adeleNorm_pos _)

theorem detNorm_ratGL (γ : BinaryRationalGL) :
    detNorm (GeneralLinearGroup.map rationalAdele γ) = 1 := by
  have h : adeleNorm (GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele γ)) = 1 := by
    rw [GeneralLinearGroup.map_det]
    exact EisensteinRegularization.Helpers.adeleNorm_rational _
  simp only [detNorm, h, NNReal.coe_one]

theorem detNorm_ratGL_mul (γ : BinaryRationalGL) (x : BinaryAdelicGL) :
    detNorm (GeneralLinearGroup.map rationalAdele γ * x) = detNorm x := by
  rw [detNorm_mul, detNorm_ratGL, one_mul]

theorem detNorm_atInfinity (r : BinaryRealGL) : detNorm (atInfinity r) = |r.val.det| :=
  PlaneEisensteinContinuation.Norm.adeleNorm_det_atInfinity r

theorem detNorm_atFinite_integral (m : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    detNorm (atFinite (GeneralLinearGroup.map integralEmbedding m)) = 1 := by
  simp [detNorm, PlaneEisensteinContinuation.Norm.adeleNorm_det_integral m]

theorem continuous_binaryDet :
    Continuous (GeneralLinearGroup.det : BinaryAdelicGL → Adelesˣ) := by
  have hdet : Continuous (Matrix.det : Matrix (Fin 2) (Fin 2) Adeles → Adeles) :=
    continuous_id.matrix_det
  exact Units.continuous_iff.mpr
    ⟨hdet.comp Units.continuous_val, hdet.comp (Units.continuous_val.comp continuous_inv)⟩

theorem continuous_detNorm : Continuous detNorm :=
  NNReal.continuous_coe.comp
    (EisensteinRegularization.Helpers.adeleNorm_continuous.comp continuous_binaryDet)

/-- The shell `1 ≤ ‖det x‖_𝔸 < 2`. -/
def shell : Set BinaryAdelicGL := detNorm ⁻¹' Ico 1 2

theorem mem_shell {x : BinaryAdelicGL} : x ∈ shell ↔ 1 ≤ detNorm x ∧ detNorm x < 2 := Iff.rfl

theorem measurableSet_shell : MeasurableSet shell :=
  continuous_detNorm.measurable measurableSet_Ico

theorem ratGL_mul_mem_shell (γ : BinaryRationalGL) (x : BinaryAdelicGL) :
    GeneralLinearGroup.map rationalAdele γ * x ∈ shell ↔ x ∈ shell := by
  simp only [mem_shell, detNorm_ratGL_mul]

theorem mul_right_mem_shell {g : BinaryAdelicGL} (hg : detNorm g = 1) (x : BinaryAdelicGL) :
    x * g ∈ shell ↔ x ∈ shell := by
  simp only [mem_shell, detNorm_mul, hg, mul_one]

/-- Any positive value of the idelic determinant norm is reached by a real central dilation. -/
theorem exists_scalar_detNorm (x : BinaryAdelicGL) (s : ℝ) (hs : 0 < s) :
    ∃ t : Adelesˣ, detNorm (GeneralLinearGroup.scalar (Fin 2) t * x) = s := by
  have hq : 0 < s / detNorm x := div_pos hs (detNorm_pos x)
  obtain ⟨u, hu0, hu⟩ : ∃ u : ℝ, 0 < u ∧ u ^ 2 = s / detNorm x :=
    ⟨Real.sqrt (s / detNorm x), Real.sqrt_pos.mpr hq, Real.sq_sqrt hq.le⟩
  refine ⟨realAdeleUnit (Units.mk0 u hu0.ne'), ?_⟩
  have h1 : detNorm (GeneralLinearGroup.scalar (Fin 2) (realAdeleUnit (Units.mk0 u hu0.ne'))) =
      u ^ 2 := by
    unfold detNorm
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow, NNReal.coe_pow,
      EisensteinRegularization.Helpers.adeleNorm_realAdeleUnit]
    simp [abs_of_pos hu0]
  rw [detNorm_mul, h1, hu]
  exact div_mul_cancel₀ _ (detNorm_pos x).ne'

/-! ## 4. Finite covolume -/

/-- The Siegel box in `GL₂(ℝ)`. -/
def siegelBox : Set BinaryRealGL := strip 1 2 (Ico (-1) 1) (Ici (1 / 2))

/-- The image of `GL₂(Ẑ)` in `GL₂(𝔸_f)`. -/
def intRange : Set BinaryFiniteGL :=
  Set.range (GeneralLinearGroup.map integralEmbedding :
    GeneralLinearGroup (Fin 2) IntegralAdeles →* BinaryFiniteGL)

theorem isCompact_intRange : IsCompact intRange := by
  let _ : CompactSpace (Matrix (Fin 2) (Fin 2) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → IntegralAdeles))
  exact isCompact_range BinaryLevel.integralMap_continuous

/-- The set `Σ × GL₂(Ẑ)` inside `GL₂(𝔸) ≃ GL₂(ℝ) × GL₂(𝔸_f)`. -/
def coverSet : Set BinaryAdelicGL :=
  (BinaryProductHaar.combineHomeomorph.toMeasurableEquiv.symm) ⁻¹' (siegelBox ×ˢ intRange)

theorem measure_coverSet_lt_top : BinaryHaar.measure coverSet < ⊤ := by
  have h := (MeasurePreserving.symm _ BinaryProductHaar.measurePreserving).measure_preimage_equiv
    (siegelBox ×ˢ intRange)
  unfold coverSet
  rw [h, Measure.prod_prod]
  refine ENNReal.mul_lt_top ?_ ?_
  · exact measure_siegel_lt_top BinaryProductHaar.realMeasure one_pos (by norm_num)
  · exact isCompact_intRange.measure_lt_top

theorem coe_smul_I (r : BinaryRealGL) (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val) :
    (((r • UpperHalfPlane.I : UpperHalfPlane) : ℂ).re = orbitRe r) ∧
      (((r • UpperHalfPlane.I : UpperHalfPlane) : ℂ).im = orbitIm r) := by
  have e1 : ((r.val 0 0 : ℝ) * Complex.I + (r.val 0 1 : ℝ)).re = r.val 0 1 := by simp
  have e2 : ((r.val 0 0 : ℝ) * Complex.I + (r.val 0 1 : ℝ)).im = r.val 0 0 := by simp
  have e3 : ((r.val 1 0 : ℝ) * Complex.I + (r.val 1 1 : ℝ)).re = r.val 1 1 := by simp
  have e4 : ((r.val 1 0 : ℝ) * Complex.I + (r.val 1 1 : ℝ)).im = r.val 1 0 := by simp
  have e5 : Complex.normSq ((r.val 1 0 : ℝ) * Complex.I + (r.val 1 1 : ℝ)) =
      r.val 1 0 ^ 2 + r.val 1 1 ^ 2 := by
    rw [Complex.normSq_apply, e3, e4]
    ring
  rw [UpperHalfPlane.coe_smul_of_det_pos hr]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, UpperHalfPlane.coe_I]
  constructor
  · rw [Complex.div_re, e1, e2, e3, e4, e5, ← add_div]
    unfold orbitRe rowNormSq
    congr 1
    ring
  · rw [Complex.div_im, e1, e2, e3, e4, e5, ← sub_div]
    unfold orbitIm rowNormSq
    rw [Matrix.det_fin_two]

theorem exists_sl_mapGL_mem_box (r : BinaryRealGL) (hr : 0 < (GeneralLinearGroup.det r : ℝˣ).val) :
    ∃ g : SpecialLinearGroup (Fin 2) ℤ,
      GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ g * r) = GeneralLinearGroup.det r ∧
      orbitRe (SpecialLinearGroup.mapGL ℝ g * r) ∈ Ico (-1 : ℝ) 1 ∧
      orbitIm (SpecialLinearGroup.mapGL ℝ g * r) ∈ Ici (1 / 2 : ℝ) := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd (r • UpperHalfPlane.I)
  have hdet : GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ g * r) =
      GeneralLinearGroup.det r := by
    rw [map_mul, SpecialLinearGroup.det_mapGL, one_mul]
  have hr' : 0 < (GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ g * r) : ℝˣ).val := by
    rw [hdet]
    exact hr
  have hsm : (SpecialLinearGroup.mapGL ℝ g * r) • UpperHalfPlane.I =
      g • (r • UpperHalfPlane.I) := by
    rw [mul_smul]
    rfl
  obtain ⟨hre, him⟩ := coe_smul_I _ hr'
  rw [hsm] at hre him
  generalize g • (r • UpperHalfPlane.I) = w at hg hre him
  have h1 : 1 ≤ Complex.normSq (w : ℂ) := hg.1
  have h2 : |(w : ℂ).re| ≤ 1 / 2 := hg.2
  have h3 : 0 < (w : ℂ).im := w.im_pos
  have h4 : Complex.normSq (w : ℂ) = (w : ℂ).re * (w : ℂ).re + (w : ℂ).im * (w : ℂ).im :=
    Complex.normSq_apply _
  obtain ⟨h7, h8⟩ := abs_le.mp h2
  refine ⟨g, hdet, ?_, ?_⟩
  · rw [← hre]
    exact ⟨by linarith, by linarith⟩
  · rw [← him]
    show 1 / 2 ≤ (w : ℂ).im
    nlinarith [mul_nonneg (sub_nonneg.2 h8) (by linarith : (0 : ℝ) ≤ (w : ℂ).re + 1 / 2)]

theorem inf_fin_mul_fin_inf (r₁ r₂ : BinaryRealGL) (k₁ k₂ : BinaryFiniteGL) :
    atInfinity r₁ * atFinite k₁ * (atFinite k₂ * atInfinity r₂) =
      atFinite (k₁ * k₂) * atInfinity (r₁ * r₂) := by
  have hc₁ : atInfinity r₁ * atFinite k₁ = atFinite k₁ * atInfinity r₁ :=
    (FiniteLevel.atFinite_atInfinity_commute k₁ r₁).symm
  have hc₂ : atInfinity r₁ * atFinite k₂ = atFinite k₂ * atInfinity r₁ :=
    (FiniteLevel.atFinite_atInfinity_commute k₂ r₁).symm
  rw [FiniteLevel.atFinite_mul, Height.atInfinity_mul, hc₁]
  calc atFinite k₁ * atInfinity r₁ * (atFinite k₂ * atInfinity r₂)
      = atFinite k₁ * (atInfinity r₁ * atFinite k₂) * atInfinity r₂ := by simp only [mul_assoc]
    _ = atFinite k₁ * (atFinite k₂ * atInfinity r₁) * atInfinity r₂ := by rw [hc₂]
    _ = atFinite k₁ * atFinite k₂ * (atInfinity r₁ * atInfinity r₂) := by simp only [mul_assoc]

/-- Every point of the shell has a rational translate in `Σ × GL₂(Ẑ)`. -/
theorem exists_cover (x : BinaryAdelicGL) (hx : x ∈ shell) :
    ∃ γ : BinaryRationalGL, γ • x ∈ coverSet := by
  obtain ⟨ρ, m, r, hr, hxeq⟩ := BinaryAdelicReduction.exists_rational_integral_positive x
  have hdr : 0 < r.val.det := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact hr
  have hnorm : detNorm x = r.val.det := by
    rw [hxeq, detNorm_mul, detNorm_mul, detNorm_ratGL, detNorm_atFinite_integral,
      detNorm_atInfinity, abs_of_pos hdr]
    ring
  have hx' : r.val.det ∈ Icc (1 : ℝ) 2 :=
    ⟨by rw [← hnorm]; exact hx.1, by rw [← hnorm]; exact hx.2.le⟩
  obtain ⟨g, hdet, hre, him⟩ := exists_sl_mapGL_mem_box r hr
  have hdet' : (SpecialLinearGroup.mapGL ℝ g * r).val.det = r.val.det := by
    rw [← GeneralLinearGroup.val_det_apply, hdet, GeneralLinearGroup.val_det_apply]
  refine ⟨SpecialLinearGroup.mapGL ℚ g * ρ⁻¹, ?_⟩
  have h1 : GeneralLinearGroup.map rationalAdele (SpecialLinearGroup.mapGL ℚ g * ρ⁻¹) * x =
      GeneralLinearGroup.map rationalAdele (SpecialLinearGroup.mapGL ℚ g) *
        (atFinite (GeneralLinearGroup.map integralEmbedding m) * atInfinity r) := by
    rw [hxeq, map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
  have hy : (SpecialLinearGroup.mapGL ℚ g * ρ⁻¹) • x =
      BinaryProductHaar.combineEquiv (SpecialLinearGroup.mapGL ℝ g * r,
        GeneralLinearGroup.map integralEmbedding (SpecialLinearGroup.mapGL IntegralAdeles g * m)) := by
    rw [BinaryProductHaar.combine_eq, GodementUnfolding.rational_smul, h1,
      ArithmeticModularity.rational_decomposition g, map_mul]
    exact inf_fin_mul_fin_inf _ _ _ _
  have hmem : (BinaryProductHaar.combineHomeomorph.toMeasurableEquiv.symm)
      ((SpecialLinearGroup.mapGL ℚ g * ρ⁻¹) • x) =
      (SpecialLinearGroup.mapGL ℝ g * r,
        GeneralLinearGroup.map integralEmbedding (SpecialLinearGroup.mapGL IntegralAdeles g * m)) := by
    rw [hy]
    exact BinaryProductHaar.combineEquiv.symm_apply_apply _
  refine Set.mem_preimage.mpr ?_
  rw [hmem]
  refine ⟨⟨?_, hre, him⟩, ⟨SpecialLinearGroup.mapGL IntegralAdeles g * m, rfl⟩⟩
  rw [hdet']
  exact hx'

/-- **Finite covolume**: `GL₂(ℚ) Z(ℝ)⁺ \ GL₂(𝔸)` has finite volume. -/
theorem measure_domain_inter_shell_lt_top :
    BinaryHaar.measure (BinaryFundamentalDomain.domain ∩ shell) < ⊤ :=
  lt_of_le_of_lt
    (measure_inter_le_of_cover BinaryFundamentalDomain.domain_fundamental exists_cover)
    measure_coverSet_lt_top

/-! ## 5. The pairing -/

/-- Left `GL₂(ℚ)`-invariance and central character `χ`. -/
structure PetAdm (χ : Adelesˣ →* ℂ) (φ : BinaryAdelicGL → ℂ) : Prop where
  leftRational : ∀ (γ : BinaryRationalGL) (x : BinaryAdelicGL),
    φ (GeneralLinearGroup.map rationalAdele γ * x) = φ x
  central : ∀ (t : Adelesˣ) (x : BinaryAdelicGL),
    φ (GeneralLinearGroup.scalar (Fin 2) t * x) = χ t * φ x

/-- The functions on which the Petersson pairing is a positive definite Hermitian form:
left `GL₂(ℚ)`-invariant, central character `χ`, bounded and continuous. -/
structure PetMem (χ : Adelesˣ →* ℂ) (φ : BinaryAdelicGL → ℂ) : Prop extends PetAdm χ φ where
  bounded : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C
  continuous : Continuous φ

/-- The integrand `1_S · conj φ · ψ` of the Petersson pairing. -/
def petIntegrand (φ ψ : BinaryAdelicGL → ℂ) (x : BinaryAdelicGL) : ℂ :=
  shell.indicator (fun y => starRingEnd ℂ (φ y) * ψ y) x

/-- The Petersson pairing `⟪φ, ψ⟫ = ∫_{D ∩ S} conj φ · ψ`, conjugate linear in `φ`. -/
def pet (φ ψ : BinaryAdelicGL → ℂ) : ℂ :=
  ∫ x in BinaryFundamentalDomain.domain, petIntegrand φ ψ x ∂BinaryHaar.measure

/-- The real quantity `∫_{D ∩ S} ‖φ‖²`. -/
def petNormSq (φ : BinaryAdelicGL → ℂ) : ℝ :=
  ∫ x in BinaryFundamentalDomain.domain, shell.indicator (fun y => ‖φ y‖ ^ 2) x
    ∂BinaryHaar.measure

/-! ### Right invariance -/

theorem petIntegrand_ratGL {φ ψ : BinaryAdelicGL → ℂ}
    (hφ : ∀ (γ : BinaryRationalGL) (x : BinaryAdelicGL),
      φ (GeneralLinearGroup.map rationalAdele γ * x) = φ x)
    (hψ : ∀ (γ : BinaryRationalGL) (x : BinaryAdelicGL),
      ψ (GeneralLinearGroup.map rationalAdele γ * x) = ψ x)
    (γ : BinaryRationalGL) (x : BinaryAdelicGL) :
    petIntegrand φ ψ (γ • x) = petIntegrand φ ψ x := by
  have hs : γ • x ∈ shell ↔ x ∈ shell := ratGL_mul_mem_shell γ x
  have h1 : φ (γ • x) = φ x := hφ γ x
  have h2 : ψ (γ • x) = ψ x := hψ γ x
  unfold petIntegrand
  by_cases hx : x ∈ shell
  · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hs.mpr hx), h1, h2]
  · simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hs.mp h))]

theorem indicator_shell_mul_right (F : BinaryAdelicGL → ℂ) {g : BinaryAdelicGL}
    (hg : detNorm g = 1) (x : BinaryAdelicGL) :
    shell.indicator (fun y => F (y * g)) x = shell.indicator F (x * g) := by
  by_cases hx : x ∈ shell
  · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem ((mul_right_mem_shell hg x).mpr hx)]
  · simp only [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun h => hx ((mul_right_mem_shell hg x).mp h))]

/-- The integral over the fundamental domain of a left-invariant function is right invariant
under translation. -/
theorem setIntegral_mul_right_domain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : BinaryAdelicGL → E)
    (hH : ∀ (γ : BinaryRationalGL) (x : BinaryAdelicGL), H (γ • x) = H x)
    (g : BinaryAdelicGL) :
    ∫ x in BinaryFundamentalDomain.domain, H (x * g) ∂BinaryHaar.measure =
      ∫ x in BinaryFundamentalDomain.domain, H x ∂BinaryHaar.measure := by
  have hD := BinaryFundamentalDomain.domain_fundamental
  have hmp : MeasurePreserving (fun y : BinaryAdelicGL => y * g⁻¹) BinaryHaar.measure
      BinaryHaar.measure := measurePreserving_mul_right BinaryHaar.measure g⁻¹
  have hs : IsFundamentalDomain BinaryRationalGL
      ((fun y : BinaryAdelicGL => y * g⁻¹) ⁻¹' BinaryFundamentalDomain.domain)
      BinaryHaar.measure :=
    hD.preimage_of_equiv (e := id) hmp.quasiMeasurePreserving Function.bijective_id
      (fun γ y => by
        show (GeneralLinearGroup.map rationalAdele γ * y) * g⁻¹ =
          GeneralLinearGroup.map rationalAdele γ * (y * g⁻¹)
        exact mul_assoc _ _ _)
  have hpre : BinaryFundamentalDomain.domain =
      (fun x : BinaryAdelicGL => x * g) ⁻¹'
        ((fun y : BinaryAdelicGL => y * g⁻¹) ⁻¹' BinaryFundamentalDomain.domain) := by
    ext x
    simp
  have hemb : MeasurableEmbedding (fun x : BinaryAdelicGL => x * g) :=
    (Homeomorph.mulRight g).measurableEmbedding
  have h1 := (measurePreserving_mul_right BinaryHaar.measure g).setIntegral_preimage_emb hemb H
    ((fun y : BinaryAdelicGL => y * g⁻¹) ⁻¹' BinaryFundamentalDomain.domain)
  rw [← hpre] at h1
  rw [h1]
  exact hs.setIntegral_eq hD hH

/-- Right invariance for translates by elements of idelic determinant norm one. -/
theorem pet_right_of_detNorm_one {φ ψ : BinaryAdelicGL → ℂ}
    (hφ : ∀ (γ : BinaryRationalGL) (x : BinaryAdelicGL),
      φ (GeneralLinearGroup.map rationalAdele γ * x) = φ x)
    (hψ : ∀ (γ : BinaryRationalGL) (x : BinaryAdelicGL),
      ψ (GeneralLinearGroup.map rationalAdele γ * x) = ψ x)
    {g : BinaryAdelicGL} (hg : detNorm g = 1) :
    pet (fun x => φ (x * g)) (fun x => ψ (x * g)) = pet φ ψ := by
  have hfun : petIntegrand (fun x => φ (x * g)) (fun x => ψ (x * g)) =
      fun x => petIntegrand φ ψ (x * g) := by
    funext x
    exact indicator_shell_mul_right (fun y => starRingEnd ℂ (φ y) * ψ y) hg x
  unfold pet
  rw [hfun]
  exact setIntegral_mul_right_domain (petIntegrand φ ψ) (petIntegrand_ratGL hφ hψ) g

/-- **Right invariance of the Petersson pairing** under all of `GL₂(𝔸)`. -/
theorem pet_right_invariant {χ : Adelesˣ →* ℂ} (hχ : ∀ t, ‖χ t‖ = 1)
    {φ ψ : BinaryAdelicGL → ℂ} (hφ : PetAdm χ φ) (hψ : PetAdm χ ψ) (g : BinaryAdelicGL) :
    pet (fun x => φ (x * g)) (fun x => ψ (x * g)) = pet φ ψ := by
  obtain ⟨t, ht⟩ := exists_scalar_detNorm g 1 one_pos
  have hcent : ∀ y, starRingEnd ℂ (φ (GeneralLinearGroup.scalar (Fin 2) t * y)) *
      ψ (GeneralLinearGroup.scalar (Fin 2) t * y) = starRingEnd ℂ (φ y) * ψ y := by
    intro y
    have h1 : starRingEnd ℂ (χ t) * χ t = 1 := by
      rw [Complex.conj_mul', hχ t]
      simp
    rw [hφ.central, hψ.central, map_mul]
    calc starRingEnd ℂ (χ t) * starRingEnd ℂ (φ y) * (χ t * ψ y)
        = (starRingEnd ℂ (χ t) * χ t) * (starRingEnd ℂ (φ y) * ψ y) := by ring
      _ = starRingEnd ℂ (φ y) * ψ y := by rw [h1, one_mul]
  have hx : ∀ y : BinaryAdelicGL, y * (GeneralLinearGroup.scalar (Fin 2) t * g) =
      GeneralLinearGroup.scalar (Fin 2) t * (y * g) := by
    intro y
    rw [← mul_assoc, ← Unimodular.scalar_commute t y, mul_assoc]
  have hfun : petIntegrand (fun x => φ (x * g)) (fun x => ψ (x * g)) =
      petIntegrand (fun x => φ (x * (GeneralLinearGroup.scalar (Fin 2) t * g)))
        (fun x => ψ (x * (GeneralLinearGroup.scalar (Fin 2) t * g))) := by
    funext x
    unfold petIntegrand
    simp only [hx, hcent]
  have key : pet (fun x => φ (x * g)) (fun x => ψ (x * g)) =
      pet (fun x => φ (x * (GeneralLinearGroup.scalar (Fin 2) t * g)))
        (fun x => ψ (x * (GeneralLinearGroup.scalar (Fin 2) t * g))) := by
    unfold pet
    rw [hfun]
  rw [key]
  exact pet_right_of_detNorm_one hφ.leftRational hψ.leftRational ht

/-! ### The space `petSpace χ` -/

namespace PetMem

variable {χ : Adelesˣ →* ℂ} {φ ψ : BinaryAdelicGL → ℂ}

theorem zero : PetMem χ (0 : BinaryAdelicGL → ℂ) where
  leftRational _ _ := rfl
  central _ _ := by simp
  bounded := ⟨0, fun x => by simp⟩
  continuous := continuous_const

theorem add (hφ : PetMem χ φ) (hψ : PetMem χ ψ) : PetMem χ (φ + ψ) where
  leftRational γ x := by simp only [Pi.add_apply, hφ.leftRational, hψ.leftRational]
  central t x := by simp only [Pi.add_apply, hφ.central, hψ.central, mul_add]
  bounded := by
    obtain ⟨C, hC⟩ := hφ.bounded
    obtain ⟨D, hD⟩ := hψ.bounded
    exact ⟨C + D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩
  continuous := hφ.continuous.add hψ.continuous

theorem smul (c : ℂ) (hφ : PetMem χ φ) : PetMem χ (c • φ) where
  leftRational γ x := by simp only [Pi.smul_apply, hφ.leftRational]
  central t x := by
    simp only [Pi.smul_apply, hφ.central, smul_eq_mul]
    ring
  bounded := by
    obtain ⟨C, hC⟩ := hφ.bounded
    refine ⟨‖c‖ * C, fun x => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
  continuous := hφ.continuous.const_smul c

/-- Right translates stay in the space. -/
theorem translate (hφ : PetMem χ φ) (g : BinaryAdelicGL) :
    PetMem χ (fun x => φ (x * g)) where
  leftRational γ x := by
    show φ (GeneralLinearGroup.map rationalAdele γ * x * g) = φ (x * g)
    rw [mul_assoc]
    exact hφ.leftRational γ (x * g)
  central t x := by
    show φ (GeneralLinearGroup.scalar (Fin 2) t * x * g) = χ t * φ (x * g)
    rw [mul_assoc]
    exact hφ.central t (x * g)
  bounded := by
    obtain ⟨C, hC⟩ := hφ.bounded
    exact ⟨C, fun x => hC _⟩
  continuous := hφ.continuous.comp (continuous_id.mul continuous_const)

end PetMem

/-- The space of bounded continuous left-`GL₂(ℚ)`-invariant functions on `GL₂(𝔸)` with central
character `χ`. -/
def petSpace (χ : Adelesˣ →* ℂ) : Submodule ℂ (BinaryAdelicGL → ℂ) where
  carrier := {φ | PetMem χ φ}
  add_mem' := fun {_ _} h₁ h₂ => PetMem.add h₁ h₂
  zero_mem' := PetMem.zero
  smul_mem' := fun c _ h => PetMem.smul c h

theorem petMem_of_mem {χ : Adelesˣ →* ℂ} (φ : petSpace χ) : PetMem χ φ.1 := φ.2

/-! ### Integrability (finite covolume) -/

theorem integrable_indicator_shell {E : Type*} [NormedAddCommGroup E] {F : BinaryAdelicGL → E}
    (hF : Continuous F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) :
    Integrable (shell.indicator F)
      (BinaryHaar.measure.restrict BinaryFundamentalDomain.domain) := by
  rw [integrable_indicator_iff measurableSet_shell]
  unfold IntegrableOn
  rw [Measure.restrict_restrict measurableSet_shell]
  have hfin : BinaryHaar.measure (shell ∩ BinaryFundamentalDomain.domain) ≠ ⊤ := by
    rw [Set.inter_comm]
    exact measure_domain_inter_shell_lt_top.ne
  exact Measure.integrableOn_of_bounded (M := C) hfin hF.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

theorem PetMem.integrable_pet {χ : Adelesˣ →* ℂ} {φ ψ : BinaryAdelicGL → ℂ}
    (hφ : PetMem χ φ) (hψ : PetMem χ ψ) :
    Integrable (petIntegrand φ ψ)
      (BinaryHaar.measure.restrict BinaryFundamentalDomain.domain) := by
  obtain ⟨Cφ, hCφ⟩ := hφ.bounded
  obtain ⟨Cψ, hCψ⟩ := hψ.bounded
  refine integrable_indicator_shell (F := fun y => starRingEnd ℂ (φ y) * ψ y)
    ((Complex.continuous_conj.comp hφ.continuous).mul hψ.continuous) (C := Cφ * Cψ) fun x => ?_
  show ‖starRingEnd ℂ (φ x) * ψ x‖ ≤ Cφ * Cψ
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hCφ x) (hCψ x) (norm_nonneg _) ((norm_nonneg _).trans (hCφ x))

/-! ### Hermitian structure -/

theorem pet_conj_symm (φ ψ : BinaryAdelicGL → ℂ) : starRingEnd ℂ (pet ψ φ) = pet φ ψ := by
  unfold pet
  rw [← integral_conj]
  congr 1
  funext x
  unfold petIntegrand
  by_cases hx : x ∈ shell
  · simp only [Set.indicator_of_mem hx, map_mul, Complex.conj_conj]
    ring
  · simp [Set.indicator_of_notMem hx]

theorem pet_smul_left (c : ℂ) (φ ψ : BinaryAdelicGL → ℂ) :
    pet (c • φ) ψ = starRingEnd ℂ c * pet φ ψ := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext x
  unfold petIntegrand
  by_cases hx : x ∈ shell
  · simp only [Set.indicator_of_mem hx, Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  · simp [Set.indicator_of_notMem hx]

theorem pet_add_left {χ : Adelesˣ →* ℂ} {φ₁ φ₂ ψ : BinaryAdelicGL → ℂ}
    (h₁ : PetMem χ φ₁) (h₂ : PetMem χ φ₂) (hψ : PetMem χ ψ) :
    pet (φ₁ + φ₂) ψ = pet φ₁ ψ + pet φ₂ ψ := by
  have hfun : petIntegrand (φ₁ + φ₂) ψ =
      fun x => petIntegrand φ₁ ψ x + petIntegrand φ₂ ψ x := by
    funext x
    unfold petIntegrand
    by_cases hx : x ∈ shell
    · simp only [Set.indicator_of_mem hx, Pi.add_apply, map_add]
      ring
    · simp [Set.indicator_of_notMem hx]
  unfold pet
  rw [hfun]
  exact integral_add (h₁.integrable_pet hψ) (h₂.integrable_pet hψ)

theorem pet_self_eq (φ : BinaryAdelicGL → ℂ) : pet φ φ = (petNormSq φ : ℂ) := by
  have key : petIntegrand φ φ =
      fun x => ((shell.indicator (fun y => ‖φ y‖ ^ 2) x : ℝ) : ℂ) := by
    funext x
    unfold petIntegrand
    by_cases hx : x ∈ shell
    · simp only [Set.indicator_of_mem hx]
      exact_mod_cast Complex.conj_mul' (φ x)
    · simp [Set.indicator_of_notMem hx]
  unfold pet petNormSq
  rw [key]
  exact integral_ofReal

theorem petNormSq_nonneg (φ : BinaryAdelicGL → ℂ) : 0 ≤ petNormSq φ :=
  integral_nonneg fun x => Set.indicator_nonneg (fun _ _ => sq_nonneg _) x

/-- The pairing of a function with itself is a nonnegative real number. -/
theorem pet_self_nonneg (φ : BinaryAdelicGL → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ pet φ φ = (r : ℂ) :=
  ⟨petNormSq φ, petNormSq_nonneg φ, pet_self_eq φ⟩

/-! ### Definiteness -/

/-- The set where `φ` is nonzero inside the shell. -/
def supportShell (φ : BinaryAdelicGL → ℂ) : Set BinaryAdelicGL :=
  {x | x ∈ shell ∧ φ x ≠ 0}

/-- **Positivity**: a continuous function in the space with `⟪φ, φ⟫ = 0` vanishes. -/
theorem eq_zero_of_pet_self_eq_zero {χ : Adelesˣ →* ℂ} (hχ : ∀ t, ‖χ t‖ = 1)
    {φ : BinaryAdelicGL → ℂ} (hφ : PetMem χ φ) (h : pet φ φ = 0) : φ = 0 := by
  have h0 : petNormSq φ = 0 := by
    rw [pet_self_eq] at h
    exact_mod_cast h
  obtain ⟨C, hC⟩ := hφ.bounded
  have hint : Integrable (shell.indicator (fun y => ‖φ y‖ ^ 2))
      (BinaryHaar.measure.restrict BinaryFundamentalDomain.domain) :=
    integrable_indicator_shell (F := fun y => ‖φ y‖ ^ 2) (hφ.continuous.norm.pow 2) (C := C ^ 2)
      fun x => by
        show ‖‖φ x‖ ^ 2‖ ≤ C ^ 2
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
  have hnn : 0 ≤ᵐ[BinaryHaar.measure.restrict BinaryFundamentalDomain.domain]
      shell.indicator (fun y => ‖φ y‖ ^ 2) :=
    Filter.Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => sq_nonneg _) x
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp h0
  have hae' : ∀ᵐ x ∂BinaryHaar.measure, x ∈ BinaryFundamentalDomain.domain →
      shell.indicator (fun y => ‖φ y‖ ^ 2) x = 0 :=
    (ae_restrict_iff' BinaryFundamentalDomain.domain_measurable).mp hae
  have hnullDA : BinaryHaar.measure (BinaryFundamentalDomain.domain ∩ supportShell φ) = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hae')
    rintro x ⟨hxD, hxS, hxφ⟩
    refine fun hcon => ?_
    have h1 := hcon hxD
    rw [Set.indicator_of_mem hxS] at h1
    exact hxφ (by simpa using h1)
  have hsmul : ∀ γ : BinaryRationalGL, γ • supportShell φ = supportShell φ := by
    intro γ
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have e : γ⁻¹ • x = GeneralLinearGroup.map rationalAdele γ⁻¹ * x := rfl
    simp only [supportShell, Set.mem_ofPred_eq]
    rw [e, ratGL_mul_mem_shell, hφ.leftRational]
  have hD := BinaryFundamentalDomain.domain_fundamental
  have hAnull : BinaryHaar.measure (supportShell φ) = 0 := by
    rw [hD.measure_eq_tsum (supportShell φ)]
    have hterm : ∀ γ : BinaryRationalGL,
        BinaryHaar.measure (γ • supportShell φ ∩ BinaryFundamentalDomain.domain) = 0 := by
      intro γ
      rw [hsmul γ, Set.inter_comm]
      exact hnullDA
    simp [hterm]
  have hU : IsOpen ({x : BinaryAdelicGL | 1 < detNorm x} ∩
      ({x : BinaryAdelicGL | detNorm x < 2} ∩ {x : BinaryAdelicGL | φ x ≠ 0})) :=
    (isOpen_lt continuous_const continuous_detNorm).inter
      ((isOpen_lt continuous_detNorm continuous_const).inter
        (isOpen_ne_fun hφ.continuous continuous_const))
  have hUnull : BinaryHaar.measure ({x : BinaryAdelicGL | 1 < detNorm x} ∩
      ({x : BinaryAdelicGL | detNorm x < 2} ∩ {x : BinaryAdelicGL | φ x ≠ 0})) = 0 := by
    refine measure_mono_null ?_ hAnull
    rintro x ⟨h1, h2, h3⟩
    exact ⟨⟨h1.le, h2⟩, h3⟩
  have hvanish : ∀ x, 1 < detNorm x → detNorm x < 2 → φ x = 0 := by
    intro x h1 h2
    by_contra hne
    have hpos := hU.measure_pos BinaryHaar.measure ⟨x, h1, h2, hne⟩
    rw [hUnull] at hpos
    exact lt_irrefl _ hpos
  funext x
  obtain ⟨t, ht⟩ := exists_scalar_detNorm x (3 / 2) (by norm_num)
  have h1 := hvanish (GeneralLinearGroup.scalar (Fin 2) t * x) (by rw [ht]; norm_num)
    (by rw [ht]; norm_num)
  rw [hφ.central] at h1
  have hχt : χ t ≠ 0 := by
    intro h0'
    have := hχ t
    rw [h0'] at this
    simp at this
  simpa [hχt] using h1

/-! ### The inner product space and the unitary right translation -/

instance petInner (χ : Adelesˣ →* ℂ) : Inner ℂ (petSpace χ) := ⟨fun φ ψ => pet φ.1 ψ.1⟩

/-- The Petersson pairing as an `InnerProductSpace.Core` on `petSpace χ`. -/
@[instance_reducible]
def petCore (χ : Adelesˣ →* ℂ) (hχ : ∀ t, ‖χ t‖ = 1) : InnerProductSpace.Core ℂ (petSpace χ) where
  conj_inner_symm φ ψ := pet_conj_symm φ.1 ψ.1
  re_inner_nonneg φ := by
    show 0 ≤ RCLike.re (pet φ.1 φ.1)
    rw [pet_self_eq]
    simpa using petNormSq_nonneg φ.1
  add_left φ₁ φ₂ ψ := pet_add_left (petMem_of_mem φ₁) (petMem_of_mem φ₂) (petMem_of_mem ψ)
  smul_left φ ψ c := pet_smul_left c φ.1 ψ.1
  definite φ h := by
    apply Subtype.ext
    exact eq_zero_of_pet_self_eq_zero hχ (petMem_of_mem φ) h

/-- Right translation by `g` on `petSpace χ`. -/
def petTranslate (χ : Adelesˣ →* ℂ) (g : BinaryAdelicGL) : petSpace χ →ₗ[ℂ] petSpace χ where
  toFun φ := ⟨fun x => φ.1 (x * g), PetMem.translate (petMem_of_mem φ) g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Right translation is an isometry for the Petersson pairing. -/
theorem pet_petTranslate {χ : Adelesˣ →* ℂ} (hχ : ∀ t, ‖χ t‖ = 1) (g : BinaryAdelicGL)
    (φ ψ : petSpace χ) :
    pet (petTranslate χ g φ).1 (petTranslate χ g ψ).1 = pet φ.1 ψ.1 :=
  pet_right_invariant hχ (petMem_of_mem φ).toPetAdm (petMem_of_mem ψ).toPetAdm g

/-! ## 6. The adelic lifts of `Γ₁(3)` cusp forms lie in the space -/

section Lift

open TernaryPeriodPolynomials.CuspIntegral
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem continuous_liftReal {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) :
    Continuous (liftReal f) := by
  have hdet : Continuous fun r : BinaryRealGL => ((GeneralLinearGroup.det r : ℝˣ) : ℝ) := by
    simpa only [GeneralLinearGroup.val_det_apply] using continuous_det
  have hsqrt : Continuous fun r : BinaryRealGL =>
      ((Real.sqrt |((GeneralLinearGroup.det r : ℝˣ) : ℝ)| : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_abs.comp hdet))
  have hsqrt_ne : ∀ r : BinaryRealGL,
      ((Real.sqrt |((GeneralLinearGroup.det r : ℝˣ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    intro r
    rw [Ne, Complex.ofReal_eq_zero, Real.sqrt_eq_zero', not_le]
    exact abs_pos.mpr (GeneralLinearGroup.det r).ne_zero
  have hdenom : Continuous fun r : BinaryRealGL => UpperHalfPlane.denom r (UpperHalfPlane.I : ℂ) := by
    unfold UpperHalfPlane.denom
    exact ((Complex.continuous_ofReal.comp (continuous_entry 1 0)).mul continuous_const).add
      (Complex.continuous_ofReal.comp (continuous_entry 1 1))
  have hdenom_ne : ∀ r : BinaryRealGL, UpperHalfPlane.denom r (UpperHalfPlane.I : ℂ) ≠ 0 :=
    fun r => UpperHalfPlane.denom_ne_zero r UpperHalfPlane.I
  have hf : Continuous fun r : BinaryRealGL => f (r • UpperHalfPlane.I) :=
    (ModularFormClass.holo f).continuous.comp (continuous_id.smul continuous_const)
  exact ((hsqrt.zpow₀ k fun r => Or.inl (hsqrt_ne r)).mul
    (hdenom.zpow₀ (-k) fun r => Or.inl (hdenom_ne r))).mul hf

theorem isOpen_levelGroup : IsOpen (levelGroup : Set BinaryFiniteGL) := by
  refine Subgroup.isOpen_mono (H₁ := BinaryLevel.finiteCongruence) ?_
    BinaryLevel.finiteCongruence_isOpen
  rintro k ⟨m, hm, rfl⟩
  refine ⟨m, ?_, rfl⟩
  show redGL m ∈ EisensteinGraph.InnerCuspidalArithmetic.Helpers.binaryRowStabilizer
  have h1 : redGL m = 1 := hm
  rw [h1]
  exact one_mem _

theorem continuous_adelicLift {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) :
    Continuous (adelicLift f) := by
  let U : Set BinaryAdelicGL := (BinaryProductHaar.combineEquiv.symm : BinaryAdelicGL → _) ⁻¹'
    ({r : BinaryRealGL | 0 < (GeneralLinearGroup.det r : ℝˣ).val} ×ˢ (levelGroup : Set BinaryFiniteGL))
  have hdetc : Continuous fun r : BinaryRealGL => ((GeneralLinearGroup.det r : ℝˣ) : ℝ) := by
    simpa only [GeneralLinearGroup.val_det_apply] using continuous_det
  have hUopen : IsOpen U :=
    (BinaryProductHaar.split_continuous).isOpen_preimage _
      ((isOpen_lt continuous_const hdetc).prod isOpen_levelGroup)
  have hproj : Continuous fun y : BinaryAdelicGL =>
      (BinaryProductHaar.combineEquiv.symm y).1 :=
    continuous_fst.comp BinaryProductHaar.split_continuous
  have hlift : ∀ y ∈ U, adelicLift f y = liftReal f (BinaryProductHaar.combineEquiv.symm y).1 := by
    intro y hy
    obtain ⟨hpos, hlev⟩ := hy
    refine adelicLift_eq_of_isDecomp f (γ := 1) (κ := (BinaryProductHaar.combineEquiv.symm y).2) ?_
    refine ⟨hpos, hlev, ?_⟩
    have h := BinaryProductHaar.combine_eq (BinaryProductHaar.combineEquiv.symm y).1
      (BinaryProductHaar.combineEquiv.symm y).2
    rw [Prod.mk.eta, MulEquiv.apply_symm_apply] at h
    rw [map_one, one_mul, infGL_apply, finGL_apply, ← FiniteLevel.atFinite_atInfinity_commute, ← h]
  refine continuous_of_cover_nhds (s := fun γ : BinaryRationalGL => {y | ratGL γ⁻¹ * y ∈ U})
    ?_ ?_
  · intro x
    obtain ⟨γ, r, κ, h⟩ := exists_isDecomp x
    refine ⟨γ, (hUopen.preimage (continuous_const.mul continuous_id)).mem_nhds ?_⟩
    show ratGL γ⁻¹ * x ∈ U
    have hx : ratGL γ⁻¹ * x = infGL r * finGL κ := by
      rw [h.2.2, map_inv, inv_mul_cancel_left]
    rw [hx]
    refine Set.mem_preimage.mpr ?_
    have h2 : infGL r * finGL κ = BinaryProductHaar.combineEquiv (r, κ) := by
      rw [BinaryProductHaar.combine_eq, infGL_apply, finGL_apply,
        FiniteLevel.atFinite_atInfinity_commute]
    rw [h2, MulEquiv.symm_apply_apply]
    exact ⟨h.1, h.2.1⟩
  · intro γ
    have hcont : Continuous fun y : BinaryAdelicGL =>
        liftReal f (BinaryProductHaar.combineEquiv.symm (ratGL γ⁻¹ * y)).1 :=
      (continuous_liftReal f).comp (hproj.comp (continuous_const.mul continuous_id))
    refine hcont.continuousOn.congr fun y hy => ?_
    rw [← adelicLift_ratGL_mul f γ⁻¹ y]
    exact hlift _ hy

theorem petMem_adelicLift {k : ℤ} (f : CuspForm binaryRealGammaOneThree k) :
    PetMem (centralChar k) (adelicLift f) where
  leftRational := adelicLift_leftRational f
  central := adelicLift_central f
  bounded := adelicLift_bounded f
  continuous := continuous_adelicLift f

/-- The span of the right translates of the lifts lies in the Petersson space. -/
theorem span_translates_le_petSpace {k : ℤ} (S : Set (CuspForm binaryRealGammaOneThree k)) :
    Submodule.span ℂ {φ | ∃ f ∈ S, ∃ g₀ : BinaryAdelicGL, φ = fun x => adelicLift f (x * g₀)} ≤
      petSpace (centralChar k) := by
  refine Submodule.span_le.mpr ?_
  rintro φ ⟨f, -, g₀, rfl⟩
  exact (petMem_adelicLift f).translate g₀

end Lift

end TernaryPeriodPolynomials.Automorphic.Petersson
