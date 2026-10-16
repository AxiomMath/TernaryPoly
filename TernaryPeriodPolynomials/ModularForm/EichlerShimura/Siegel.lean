module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.Horoball

@[expose] public section


/-!
# Siegel sets and local finiteness of the `SL(2, ℤ)` action

`siegel` is the Siegel set `|Re z| ≤ 1`, `Im z ≥ 1/2`; it contains the standard fundamental
domain in its interior. The main result `finite_strip` says that only finitely many
`g ∈ SL(2, ℤ)` move a point of a bounded strip `y₀ ≤ Im z ≤ Y`, `|Re z| ≤ X` into `siegel`.
This is the local finiteness behind the `Γ`-partition of unity used for the equivariant
primitive in the Eichler–Shimura surjectivity route (Section 6 of the paper).

Written by Claude Opus 5.5.
-/

open UpperHalfPlane ModularGroup Complex
open scoped Modular MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations

/-- The Siegel set `|Re z| ≤ 1`, `Im z ≥ 1/2`. -/
def siegel : Set ℍ := {z | |z.re| ≤ 1 ∧ 1 / 2 ≤ z.im}

private theorem abs_le_one_add_sq (t : ℝ) : |t| ≤ 1 + t ^ 2 := by
  rcases le_total |t| 1 with h | h
  · nlinarith [sq_nonneg t]
  · have : |t| ≤ |t| ^ 2 := by nlinarith
    rw [sq_abs] at this; linarith

private theorem le_mul_of_mul_sq_le {t s k B : ℝ} (hk : s ^ 2 * k = 1) (hk0 : 0 ≤ k)
    (h : t * s ^ 2 ≤ B) : t ≤ B * k := by
  calc t = t * (s ^ 2 * k) := by rw [hk, mul_one]
    _ = t * s ^ 2 * k := by ring
    _ ≤ B * k := mul_le_mul_of_nonneg_right h hk0

private theorem abs_sub_bound {p q r A B : ℝ} (hp : |p| ≤ A) (hq : |q| ≤ B) (hr : r = p - q) :
    |r| ≤ A + B := by
  rw [hr]; exact le_trans (abs_sub _ _) (add_le_add hp hq)

private theorem bottom_bounds {c d x y v N y0 Y X k : ℝ} (hy0 : 0 < y0)
    (hyl : y0 ≤ y) (hyu : y ≤ Y) (hx : |x| ≤ X) (hv : 1 / 2 ≤ v)
    (hk : y0 ^ 2 * k = 1) (hk0 : 0 ≤ k)
    (hN : N = (c * x + d) ^ 2 + (c * y) ^ 2) (hvN : v * N = y) (hNpos : 0 < N) :
    N ≤ 2 * Y ∧ |c| ≤ 1 + 2 * Y * k ∧ |d| ≤ 1 + 2 * Y + (1 + 2 * Y * k) * X := by
  have hN2 : N ≤ 2 * Y := by
    have : 1 / 2 * N ≤ v * N := mul_le_mul_of_nonneg_right hv hNpos.le
    linarith
  have hy2 : y0 ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hy0.le hyl 2
  have hc2 : c ^ 2 * y0 ^ 2 ≤ 2 * Y := by
    have h1 : c ^ 2 * y0 ^ 2 ≤ c ^ 2 * y ^ 2 := mul_le_mul_of_nonneg_left hy2 (sq_nonneg c)
    have h2 : c ^ 2 * y ^ 2 = (c * y) ^ 2 := by ring
    have h3 := sq_nonneg (c * x + d)
    linarith
  have hcb : |c| ≤ 1 + 2 * Y * k :=
    le_trans (abs_le_one_add_sq c) (by linarith [le_mul_of_mul_sq_le hk hk0 hc2])
  have hX0 : 0 ≤ X := le_trans (abs_nonneg x) hx
  have hY : 0 ≤ Y := le_trans (le_trans hy0.le hyl) hyu
  have hcx : |c * x| ≤ (1 + 2 * Y * k) * X := by
    rw [abs_mul]; exact mul_le_mul hcb hx (abs_nonneg _) (by positivity)
  have h1 : |c * x + d| ≤ 1 + 2 * Y :=
    le_trans (abs_le_one_add_sq _) (by linarith [sq_nonneg (c * y)])
  exact ⟨hN2, hcb, abs_sub_bound h1 hcx (by ring)⟩

private theorem top_bounds {a b x y u v N y0 Y X k : ℝ} (hy0 : 0 < y0)
    (hyl : y0 ≤ y) (hyu : y ≤ Y) (hx : |x| ≤ X) (hu : |u| ≤ 1)
    (hk : y0 ^ 2 * k = 1) (hk0 : 0 ≤ k) (hvN : v * N = y) (hNpos : 0 < N) (hN2 : N ≤ 2 * Y)
    (hvb : v ≤ Y * k)
    (hwN : (u ^ 2 + v ^ 2) * N = (a * x + b) ^ 2 + (a * y) ^ 2) :
    |a| ≤ 1 + (2 * Y + Y * (Y * k)) * k ∧
      |b| ≤ 1 + (2 * Y + Y * (Y * k)) + (1 + (2 * Y + Y * (Y * k)) * k) * X := by
  have hy : 0 < y := lt_of_lt_of_le hy0 hyl
  have hY : 0 ≤ Y := le_trans hy.le hyu
  have hX0 : 0 ≤ X := le_trans (abs_nonneg x) hx
  have hu2 : u ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg u) hu 2
    rw [sq_abs, one_pow] at h; exact h
  have hRb : (a * x + b) ^ 2 + (a * y) ^ 2 ≤ 2 * Y + Y * (Y * k) := by
    rw [← hwN]
    have h1 : (u ^ 2 + v ^ 2) * N = u ^ 2 * N + v * (v * N) := by ring
    rw [h1, hvN]
    have h2 : u ^ 2 * N ≤ 1 * N := mul_le_mul_of_nonneg_right hu2 hNpos.le
    have h3 : v * y ≤ Y * k * Y := mul_le_mul hvb hyu hy.le (by positivity)
    have h4 : Y * k * Y = Y * (Y * k) := by ring
    linarith
  have hy2 : y0 ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hy0.le hyl 2
  have ha2 : a ^ 2 * y0 ^ 2 ≤ 2 * Y + Y * (Y * k) := by
    have h1 : a ^ 2 * y0 ^ 2 ≤ a ^ 2 * y ^ 2 := mul_le_mul_of_nonneg_left hy2 (sq_nonneg a)
    have h2 : a ^ 2 * y ^ 2 = (a * y) ^ 2 := by ring
    have h3 := sq_nonneg (a * x + b)
    linarith
  have hab : |a| ≤ 1 + (2 * Y + Y * (Y * k)) * k :=
    le_trans (abs_le_one_add_sq a) (by linarith [le_mul_of_mul_sq_le hk hk0 ha2])
  have hax : |a * x| ≤ (1 + (2 * Y + Y * (Y * k)) * k) * X := by
    rw [abs_mul]; exact mul_le_mul hab hx (abs_nonneg _) (by positivity)
  have h1 : |a * x + b| ≤ 1 + (2 * Y + Y * (Y * k)) :=
    le_trans (abs_le_one_add_sq _) (by linarith [sq_nonneg (a * y)])
  exact ⟨hab, abs_sub_bound h1 hax (by ring)⟩

private theorem normSq_denom_eq (g : SL(2, ℤ)) (z : ℍ) :
    Complex.normSq (denom g z) =
      (((g 1 0 : ℤ) : ℝ) * z.re + ((g 1 1 : ℤ) : ℝ)) ^ 2 + (((g 1 0 : ℤ) : ℝ) * z.im) ^ 2 := by
  rw [Complex.normSq_apply, ModularGroup.denom_apply]
  simp
  ring

private theorem smul_mul_denom (g : SL(2, ℤ)) (z : ℍ) :
    ((g • z : ℍ) : ℂ) * (((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ)) =
      ((g 0 0 : ℤ) : ℂ) * z + ((g 0 1 : ℤ) : ℂ) := by
  have hne : ((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero g z
    rw [ModularGroup.denom_apply] at this
    exact_mod_cast this
  rw [UpperHalfPlane.specialLinearGroup_apply]
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
  exact div_mul_cancel₀ _ hne

private theorem normSq_num_eq (g : SL(2, ℤ)) (z : ℍ) :
    Complex.normSq (((g 0 0 : ℤ) : ℂ) * z + ((g 0 1 : ℤ) : ℂ)) =
      (((g 0 0 : ℤ) : ℝ) * z.re + ((g 0 1 : ℤ) : ℝ)) ^ 2 + (((g 0 0 : ℤ) : ℝ) * z.im) ^ 2 := by
  rw [Complex.normSq_apply]
  simp
  ring

private theorem normSq_denom' (g : SL(2, ℤ)) (z : ℍ) :
    Complex.normSq (((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ)) =
      (((g 1 0 : ℤ) : ℝ) * z.re + ((g 1 1 : ℤ) : ℝ)) ^ 2 + (((g 1 0 : ℤ) : ℝ) * z.im) ^ 2 := by
  rw [Complex.normSq_apply]
  simp
  ring

private theorem bottom_row_int (g : SL(2, ℤ)) :
    ((g 1 0 = 0) ∧ (1 : ℝ) ≤ ((g 1 1 : ℤ) : ℝ) ^ 2) ∨ (1 : ℝ) ≤ ((g 1 0 : ℤ) : ℝ) ^ 2 := by
  by_cases hc : g 1 0 = 0
  · left
    refine ⟨hc, ?_⟩
    have hdet := g.2
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    have hd : g 1 1 ≠ 0 := by
      intro h; rw [h, mul_zero] at hdet; exact zero_ne_one hdet
    have : (1 : ℤ) ≤ g 1 1 ^ 2 := by
      have := Int.one_le_abs hd
      nlinarith [sq_abs (g 1 1)]
    exact_mod_cast this
  · right
    have : (1 : ℤ) ≤ g 1 0 ^ 2 := by
      have := Int.one_le_abs hc
      nlinarith [sq_abs (g 1 0)]
    exact_mod_cast this

/-- An explicit entry bound for `g` moving a point of the strip into `siegel`. -/
def stripBound (y0 Y X : ℝ) : ℝ :=
  let k := 1 / min y0 1 ^ 2
  (1 + 2 * Y * k) + (1 + 2 * Y + (1 + 2 * Y * k) * X) + (1 + (2 * Y + Y * (Y * k)) * k) +
    (1 + (2 * Y + Y * (Y * k)) + (1 + (2 * Y + Y * (Y * k)) * k) * X)

theorem entry_bound_of_strip {y0 Y X : ℝ} (hy0 : 0 < y0) {g : SL(2, ℤ)} {z : ℍ}
    (hyl : y0 ≤ z.im) (hyu : z.im ≤ Y) (hx : |z.re| ≤ X) (hgz : g • z ∈ siegel) (i j : Fin 2) :
    |((g i j : ℤ) : ℝ)| ≤ stripBound y0 Y X := by
  obtain ⟨hu, hv⟩ := hgz
  set y1 := min y0 1 with hy1
  have hy1p : 0 < y1 := lt_min hy0 one_pos
  have hy1l : y1 ≤ z.im := le_trans (min_le_left _ _) hyl
  set k := 1 / y1 ^ 2 with hkdef
  have hk : y1 ^ 2 * k = 1 := by rw [hkdef]; field_simp
  have hk0 : 0 ≤ k := by positivity
  have hNpos : 0 < Complex.normSq (denom g z) := Complex.normSq_pos.mpr (denom_ne_zero g z)
  have him := ModularGroup.im_smul_eq_div_normSq g z
  have hvN : (g • z).im * Complex.normSq (denom g z) = z.im := by
    rw [him]; field_simp
  have hN := normSq_denom_eq g z
  obtain ⟨hN2, hcb, hdb⟩ :=
    bottom_bounds hy1p hy1l hyu hx hv hk hk0 hN hvN hNpos
  have hNl : y1 ^ 2 ≤ Complex.normSq (denom g z) := by
    have hy2 : y1 ^ 2 ≤ z.im ^ 2 := pow_le_pow_left₀ hy1p.le hy1l 2
    have hy11 : y1 ^ 2 ≤ 1 := by
      have : y1 ≤ 1 := min_le_right _ _
      nlinarith
    rw [hN]
    rcases bottom_row_int g with ⟨hc, hd⟩ | hc
    · rw [hc]; simp only [Int.cast_zero, zero_mul, zero_add]; nlinarith
    · have : z.im ^ 2 ≤ ((g 1 0 : ℤ) : ℝ) ^ 2 * z.im ^ 2 := by
        nlinarith [sq_nonneg z.im]
      nlinarith [sq_nonneg (((g 1 0 : ℤ) : ℝ) * z.re + ((g 1 1 : ℤ) : ℝ))]
  have hvb : (g • z).im ≤ Y * k := by
    have h1 : (g • z).im * y1 ^ 2 ≤ Y := by
      have : (g • z).im * y1 ^ 2 ≤ (g • z).im * Complex.normSq (denom g z) :=
        mul_le_mul_of_nonneg_left hNl (le_trans (by norm_num) hv)
      linarith
    exact le_mul_of_mul_sq_le hk hk0 h1
  have hwN : ((g • z).re ^ 2 + (g • z).im ^ 2) * Complex.normSq (denom g z) =
      (((g 0 0 : ℤ) : ℝ) * z.re + ((g 0 1 : ℤ) : ℝ)) ^ 2 + (((g 0 0 : ℤ) : ℝ) * z.im) ^ 2 := by
    have h := congrArg Complex.normSq (smul_mul_denom g z)
    rw [Complex.normSq_mul, normSq_num_eq, normSq_denom', ← normSq_denom_eq,
      Complex.normSq_apply] at h
    rw [← h]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  obtain ⟨hab, hbb⟩ := top_bounds hy1p hy1l hyu hx hu hk hk0 hvN hNpos hN2 hvb hwN
  have hX0 : 0 ≤ X := le_trans (abs_nonneg _) hx
  have hY : 0 ≤ Y := le_trans z.im_pos.le hyu
  have p1 : 0 ≤ 1 + 2 * Y * k := by positivity
  have p2 : 0 ≤ 1 + 2 * Y + (1 + 2 * Y * k) * X := by positivity
  have p3 : 0 ≤ 1 + (2 * Y + Y * (Y * k)) * k := by positivity
  have p4 : 0 ≤ 1 + (2 * Y + Y * (Y * k)) + (1 + (2 * Y + Y * (Y * k)) * k) * X := by positivity
  simp only [stripBound]
  rw [← hy1, ← hkdef]
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]; linarith
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]; linarith
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]; linarith
  · simp only [Fin.isValue, Fin.mk_one]; linarith

/-- Only finitely many `g ∈ SL(2, ℤ)` move a point of the strip `y₀ ≤ Im z ≤ Y`, `|Re z| ≤ X`
into the Siegel set. -/
theorem finite_strip {y0 : ℝ} (hy0 : 0 < y0) (Y X : ℝ) :
    {g : SL(2, ℤ) | ∃ z : ℍ, y0 ≤ z.im ∧ z.im ≤ Y ∧ |z.re| ≤ X ∧ g • z ∈ siegel}.Finite := by
  set M : ℤ := ⌈stripBound y0 Y X⌉
  have hfin : (Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 =>
      Set.Icc (-M) M : Set (Fin 2 → Fin 2 → ℤ)).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _
  have hinj : Set.InjOn (fun (g : SL(2, ℤ)) (i j : Fin 2) => g i j) Set.univ := by
    intro g _ g' _ h
    ext i j
    exact congrFun (congrFun h i) j
  refine (hfin.preimage (hinj.mono (Set.subset_univ _))).subset ?_
  rintro g ⟨z, hyl, hyu, hx, hgz⟩
  refine fun i _ j _ => ?_
  rw [Set.mem_Icc]
  have h := entry_bound_of_strip hy0 hyl hyu hx hgz i j
  have h' : |((g i j : ℤ) : ℝ)| ≤ (M : ℝ) := le_trans h (Int.le_ceil _)
  rw [abs_le] at h'
  constructor
  · exact_mod_cast h'.1
  · exact_mod_cast h'.2

end TernaryPeriodPolynomials.Argument.ESFoundations
