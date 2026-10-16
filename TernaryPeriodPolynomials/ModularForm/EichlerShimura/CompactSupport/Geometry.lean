module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.PartitionOfUnity

@[expose] public section


/-!
# Geometry of cusp neighbourhoods in the upper half plane (functions on `ℂ`)

Foundation for step 1 of the unconditional Eichler--Shimura route.  An element `s` of `SL(2, ℤ)` with
vanishing lower-left entry translates the upper half plane by its translation length
(`mob_of_lowerLeft`); two points of the height-one horoball at `∞` related by `a` force
`a 1 0 = 0` (`lowerLeft_of_mob`); and only finitely many elements of `SL(2, ℤ)` move a point of a
small neighbourhood into a strip of bounded real part and height at least `1/2`
(`exists_finite_nbhd_re`).

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane ModularGroup Complex
open scoped Modular MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.CompactSupport

open TernaryPeriodPolynomials.Argument.ESFoundations
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)


theorem diag_of_lowerLeft {δ : SL(2, ℤ)} (hδ : δ 1 0 = 0) :
    δ 1 1 = δ 0 0 ∧ δ 0 0 * δ 0 0 = 1 := by
  have hdet : δ 0 0 * δ 1 1 = 1 := by
    have := δ.2
    rw [Matrix.det_fin_two, hδ] at this
    linarith
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · exact ⟨by rw [ha, hd], by rw [ha]; norm_num⟩
  · exact ⟨by rw [ha, hd], by rw [ha]; norm_num⟩

/-- An element fixing `∞` translates by its translation length. -/
theorem mob_of_lowerLeft {s : SL(2, ℤ)} (hs : s 1 0 = 0) {z : ℂ} (hz : z ∈ U) :
    mob s z = z + (transLen s : ℂ) := by
  obtain ⟨h1, h2⟩ := diag_of_lowerLeft hs
  rw [mob_eq s hz, hs, h1]
  have h0 : ((s 0 0 : ℤ) : ℂ) ≠ 0 := by
    intro h
    have : (s 0 0 : ℤ) = 0 := by exact_mod_cast h
    rw [this] at h2; simp at h2
  have h2' : ((s 0 0 : ℤ) : ℂ) * ((s 0 0 : ℤ) : ℂ) = 1 := by exact_mod_cast h2
  unfold transLen
  push_cast
  rw [div_eq_iff (by simpa using h0)]
  linear_combination (-((s 0 1 : ℤ) : ℂ)) * h2'

theorem im_mob_of_lowerLeft {s : SL(2, ℤ)} (hs : s 1 0 = 0) {z : ℂ} (hz : z ∈ U) :
    (mob s z).im = z.im := by
  rw [mob_of_lowerLeft hs hz]; simp

theorem re_mob_of_lowerLeft {s : SL(2, ℤ)} (hs : s 1 0 = 0) {z : ℂ} (hz : z ∈ U) :
    (mob s z).re = z.re + transLen s := by
  rw [mob_of_lowerLeft hs hz]; simp

/-- Two points of the height-one horoball at infinity related by `a` force `a` to fix `∞`. -/
theorem lowerLeft_of_mob {a : SL(2, ℤ)} {u : ℂ} (hu : u ∈ U) (h1 : 1 < u.im)
    (h2 : 1 < (mob a u).im) : a 1 0 = 0 := by
  have hz : (UpperHalfPlane.ofComplex u : ℍ) = ⟨u, hu⟩ := UpperHalfPlane.ofComplex_apply_of_im_pos hu
  apply lowerLeft_eq_zero_of_horoball (z := ⟨u, hu⟩) h1
  have : ((a • (⟨u, hu⟩ : ℍ) : ℍ) : ℂ) = mob a u := by
    rw [mob, hz]
  change 1 < ((a • (⟨u, hu⟩ : ℍ) : ℍ) : ℂ).im
  rw [this]; exact h2

theorem T_zpow_lowerLeft (j : ℤ) : (ModularGroup.T ^ j : SL(2, ℤ)) 1 0 = 0 := by
  simp [ModularGroup.coe_T_zpow]

theorem transLen_T_zpow (j : ℤ) : transLen (ModularGroup.T ^ j : SL(2, ℤ)) = j := by
  simp [transLen, ModularGroup.coe_T_zpow]

theorem mob_T_zpow (j : ℤ) {z : ℂ} (hz : z ∈ U) : mob (ModularGroup.T ^ j) z = z + (j : ℂ) := by
  rw [mob_of_lowerLeft (T_zpow_lowerLeft j) hz, transLen_T_zpow]

/-- Local finiteness of the `SL(2, ℤ)`-action with a bounded real part. -/
theorem exists_finite_nbhd_re {z₀ : ℂ} (hz₀ : z₀ ∈ U) (B : ℝ) :
    ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧ ∃ T : Finset SL(2, ℤ), ∀ z ∈ V, ∀ a : SL(2, ℤ),
      (|(mob a z).re| ≤ B ∧ 1 / 2 ≤ (mob a z).im) → a ∈ T := by
  classical
  obtain ⟨V, hVo, hzV, hVU, T₀, hT₀⟩ := exists_finite_nbhd hz₀
  set N : ℤ := ⌈B⌉ + 1 with hN
  refine ⟨V, hVo, hzV, hVU,
    ((Finset.Icc (-N) N) ×ˢ T₀).image fun p : ℤ × SL(2, ℤ) => ModularGroup.T ^ (-p.1) * p.2, ?_⟩
  intro z hz a ⟨hre, him⟩
  have hzU : z ∈ U := hVU hz
  set r := (mob a z).re with hr
  set j : ℤ := -⌊r + 1 / 2⌋ with hj
  have hmob : mob (ModularGroup.T ^ j * a) z = mob a z + (j : ℂ) := by
    rw [mob_mul, mob_T_zpow j (mob_mem a z)]
  have hf1 := Int.floor_le (r + 1 / 2)
  have hf2 := Int.lt_floor_add_one (r + 1 / 2)
  have hjr : ((j : ℤ) : ℝ) = -(⌊r + 1 / 2⌋ : ℝ) := by rw [hj]; push_cast; ring
  have hre' : |(mob (ModularGroup.T ^ j * a) z).re| ≤ 1 := by
    rw [hmob]
    simp only [Complex.add_re, Complex.intCast_re]
    rw [abs_le, hjr]
    constructor <;> linarith
  have him' : 1 / 2 ≤ (mob (ModularGroup.T ^ j * a) z).im := by
    rw [hmob]; simpa using him
  have hmem := hT₀ z hz _ ⟨hre', him'⟩
  have hjN : -N ≤ j ∧ j ≤ N := by
    have hB := Int.le_ceil B
    have hB' : (B : ℝ) ≤ (⌈B⌉ : ℝ) := hB
    have habs := abs_le.mp hre
    have hNr : (N : ℝ) = (⌈B⌉ : ℝ) + 1 := by rw [hN]; push_cast; ring
    constructor
    · have : (-(N : ℝ)) ≤ (j : ℝ) := by rw [hjr, hNr]; linarith
      exact_mod_cast this
    · have : (j : ℝ) ≤ (N : ℝ) := by rw [hjr, hNr]; linarith
      exact_mod_cast this
  rw [Finset.mem_image]
  refine ⟨(j, ModularGroup.T ^ j * a), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hjN, hmem⟩, ?_⟩
  show ModularGroup.T ^ (-j) * (ModularGroup.T ^ j * a) = a
  rw [zpow_neg, inv_mul_cancel_left]


/-! ### Conjugated powers of a cusp generator -/

theorem transLen_zpow {s : SL(2, ℤ)} (hs : s 1 0 = 0) (j : ℤ) :
    (s ^ j) 1 0 = 0 ∧ transLen (s ^ j) = j * transLen s := by
  have hmem : s ∈ stabInfty := hs
  refine ⟨stabInfty.zpow_mem hmem j, ?_⟩
  have hpow : ∀ k : ℕ, transLen (s ^ k) = k * transLen s := by
    intro k
    induction k with
    | zero => simp [transLen]
    | succ k ih =>
      have hk : (s ^ k) 1 0 = 0 := stabInfty.pow_mem hmem k
      rw [pow_succ, transLen_mul hk hs, ih]
      push_cast; ring
  rcases Int.eq_nat_or_neg j with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast]; exact_mod_cast hpow k
  · have hk : (s ^ k) 1 0 = 0 := stabInfty.pow_mem hmem k
    have hki : ((s ^ k)⁻¹) 1 0 = 0 := stabInfty.inv_mem hk
    have h0 := transLen_mul hki hk
    rw [inv_mul_cancel] at h0
    have h1 : transLen (1 : SL(2, ℤ)) = 0 := by simp [transLen]
    rw [zpow_neg, zpow_natCast]
    rw [h1] at h0
    have := hpow k
    linarith

theorem mob_conj_zpow {g a : SL(2, ℤ)} (ha : (g⁻¹ * a * g) 1 0 = 0) (j : ℤ) (w : ℂ) :
    mob g⁻¹ (mob (a ^ j) w) = mob g⁻¹ w + ((j * transLen (g⁻¹ * a * g) : ℤ) : ℂ) := by
  obtain ⟨h1, h2⟩ := transLen_zpow ha j
  have e : (g⁻¹ * a * g) ^ j = g⁻¹ * a ^ j * g := by
    have := conj_zpow (a := g⁻¹) (b := a) (i := j)
    simpa using this
  rw [e] at h1 h2
  have : mob g⁻¹ (mob (a ^ j) w) = mob (g⁻¹ * a ^ j * g) (mob g⁻¹ w) := by
    rw [← mob_mul, ← mob_mul]; congr 1; group
  rw [this, mob_of_lowerLeft h1 (mob_mem _ _), h2]


end TernaryPeriodPolynomials.Argument.ESFoundations.CompactSupport
