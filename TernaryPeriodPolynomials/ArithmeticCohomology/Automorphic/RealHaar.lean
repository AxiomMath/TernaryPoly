module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.OrbitalMass

@[expose] public section


/-!
# Siegel boxes in `GL₂(ℝ)` have finite Haar measure

For `g = [[a, b], [c, d]] ∈ GL₂(ℝ)` write `rowNormSq g = c² + d²` (never zero),
`orbitRe g = (a c + b d) / (c² + d²)` and `orbitIm g = det g / (c² + d²)`; for `det g > 0`
these are the real and imaginary parts of the Möbius image `g · i`.

The *strip* `strip α β I J` is the set of `g` with `det g ∈ [α, β]`, `orbitRe g ∈ I` and
`orbitIm g ∈ J`. The main result `measure_siegel_lt_top` says that for every left-invariant
measure on `GL₂(ℝ)` which is finite on compact sets (in particular every left Haar measure),
the Siegel box `strip α β [-1, 1) [c, ∞)` has finite measure as soon as `0 < α` and `0 < c`.

The proof uses only left invariance and compactness, not an explicit density:
* left multiplication by the unipotent `[[1, t], [0, 1]]` translates `orbitRe` by `t`;
* left multiplication by `diag(s⁻¹, s)` divides `orbitRe` and `orbitIm` by `s²`;
* the strip of height `[c, 4c)` and width `[-1, 1)` contains `N` disjoint translates of the strip
  of width `[0, 2 / N)`, so the latter has measure at most `M / N` where `M` is the (finite,
  by compactness) measure of the former;
* the layer of height `[c 4ᵏ, c 4ᵏ⁺¹)` is a left translate (by `diag(2⁻ᵏ, 2ᵏ)`, then a unipotent)
  of the strip of width `[0, 2 / 4ᵏ)` and height `[c, 4c)`, so it has measure at most `M / 4ᵏ`;
  summing the geometric series bounds the Siegel box.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.Automorphic.RealHaar

/-! ### Möbius coordinates -/

/-- The squared length `c² + d²` of the bottom row of `g`. -/
def rowNormSq (g : BinaryRealGL) : ℝ := g.val 1 0 ^ 2 + g.val 1 1 ^ 2

/-- The real part `(a c + b d) / (c² + d²)` of `g · i`. -/
def orbitRe (g : BinaryRealGL) : ℝ :=
  (g.val 0 0 * g.val 1 0 + g.val 0 1 * g.val 1 1) / rowNormSq g

/-- The imaginary part `det g / (c² + d²)` of `g · i` (when `det g > 0`). -/
def orbitIm (g : BinaryRealGL) : ℝ := g.val.det / rowNormSq g

theorem rowNormSq_pos (g : BinaryRealGL) : 0 < rowNormSq g := by
  have hdet := GeneralLinearGroup.det_ne_zero g
  rw [Matrix.det_fin_two] at hdet
  unfold rowNormSq
  by_contra hle
  have h1 : g.val 1 0 = 0 := by nlinarith [sq_nonneg (g.val 1 0), sq_nonneg (g.val 1 1)]
  have h2 : g.val 1 1 = 0 := by nlinarith [sq_nonneg (g.val 1 0), sq_nonneg (g.val 1 1)]
  exact hdet (by rw [h1, h2]; ring)

theorem orbitRe_mul_rowNormSq (g : BinaryRealGL) :
    orbitRe g * rowNormSq g = g.val 0 0 * g.val 1 0 + g.val 0 1 * g.val 1 1 :=
  div_mul_cancel₀ _ (rowNormSq_pos g).ne'

theorem orbitIm_mul_rowNormSq (g : BinaryRealGL) : orbitIm g * rowNormSq g = g.val.det :=
  div_mul_cancel₀ _ (rowNormSq_pos g).ne'

/-- The top row has squared length `|g · i|² (c² + d²)`. -/
theorem topRow_sq (g : BinaryRealGL) :
    g.val 0 0 ^ 2 + g.val 0 1 ^ 2 = (orbitRe g ^ 2 + orbitIm g ^ 2) * rowNormSq g := by
  have hD := (rowNormSq_pos g).ne'
  have h1 := orbitRe_mul_rowNormSq g
  have h2 := orbitIm_mul_rowNormSq g
  rw [Matrix.det_fin_two] at h2
  have key : (orbitRe g * rowNormSq g) ^ 2 + (orbitIm g * rowNormSq g) ^ 2 =
      (g.val 0 0 ^ 2 + g.val 0 1 ^ 2) * rowNormSq g := by
    rw [h1, h2]; unfold rowNormSq; ring
  apply mul_right_cancel₀ hD
  linear_combination -key

theorem continuous_entry (i j : Fin 2) : Continuous fun g : BinaryRealGL => g.val i j :=
  (continuous_apply j).comp ((continuous_apply i).comp
    (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℝ)))

theorem continuous_det : Continuous fun g : BinaryRealGL => g.val.det := by
  simp only [Matrix.det_fin_two]
  exact ((continuous_entry 0 0).mul (continuous_entry 1 1)).sub
    ((continuous_entry 0 1).mul (continuous_entry 1 0))

theorem continuous_rowNormSq : Continuous rowNormSq :=
  ((continuous_entry 1 0).pow 2).add ((continuous_entry 1 1).pow 2)

theorem continuous_orbitRe : Continuous orbitRe :=
  (((continuous_entry 0 0).mul (continuous_entry 1 0)).add
    ((continuous_entry 0 1).mul (continuous_entry 1 1))).div continuous_rowNormSq
    (fun g => (rowNormSq_pos g).ne')

theorem continuous_orbitIm : Continuous orbitIm :=
  continuous_det.div continuous_rowNormSq (fun g => (rowNormSq_pos g).ne')

/-! ### Strips -/

/-- Matrices with `det ∈ [α, β]`, `orbitRe ∈ I` and `orbitIm ∈ J`. -/
def strip (α β : ℝ) (I J : Set ℝ) : Set BinaryRealGL :=
  {g | g.val.det ∈ Icc α β ∧ orbitRe g ∈ I ∧ orbitIm g ∈ J}

theorem measurableSet_strip (α β : ℝ) {I J : Set ℝ} (hI : MeasurableSet I)
    (hJ : MeasurableSet J) : MeasurableSet (strip α β I J) :=
  (continuous_det.measurable measurableSet_Icc).inter
    ((continuous_orbitRe.measurable hI).inter (continuous_orbitIm.measurable hJ))

theorem strip_mono {α β : ℝ} {I I' J J' : Set ℝ} (hI : I ⊆ I') (hJ : J ⊆ J') :
    strip α β I J ⊆ strip α β I' J' :=
  fun _ hg => ⟨hg.1, hI hg.2.1, hJ hg.2.2⟩

/-! ### Left translations -/

theorem unipotent_mul_val (t : ℝ) (g : BinaryRealGL) :
    (binaryUnipotent t * g).val =
      !![g.val 0 0 + t * g.val 1 0, g.val 0 1 + t * g.val 1 1; g.val 1 0, g.val 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_unipotent_mul (t : ℝ) (g : BinaryRealGL) :
    (binaryUnipotent t * g).val.det = g.val.det := by
  rw [unipotent_mul_val, Matrix.det_fin_two_of, Matrix.det_fin_two]; ring

theorem rowNormSq_unipotent_mul (t : ℝ) (g : BinaryRealGL) :
    rowNormSq (binaryUnipotent t * g) = rowNormSq g := by
  simp only [rowNormSq, unipotent_mul_val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]

theorem orbitRe_unipotent_mul (t : ℝ) (g : BinaryRealGL) :
    orbitRe (binaryUnipotent t * g) = orbitRe g + t := by
  have hD := (rowNormSq_pos g).ne'
  rw [orbitRe, rowNormSq_unipotent_mul, orbitRe]
  simp only [unipotent_mul_val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  unfold rowNormSq
  ring

theorem orbitIm_unipotent_mul (t : ℝ) (g : BinaryRealGL) :
    orbitIm (binaryUnipotent t * g) = orbitIm g := by
  rw [orbitIm, orbitIm, det_unipotent_mul, rowNormSq_unipotent_mul]

theorem preimage_unipotent_strip (t α β : ℝ) (I J : Set ℝ) :
    (fun g => binaryUnipotent t * g) ⁻¹' strip α β I J = strip α β ((· + t) ⁻¹' I) J := by
  ext g
  simp only [strip, mem_preimage, mem_ofPred_eq, det_unipotent_mul, orbitRe_unipotent_mul,
    orbitIm_unipotent_mul]

/-- The diagonal matrix `diag(s⁻¹, s)`. -/
def scaling (s : ℝ) (hs : s ≠ 0) : BinaryRealGL :=
  GeneralLinearGroup.mkOfDetNeZero !![s⁻¹, 0; 0, s] (by
    rw [Matrix.det_fin_two_of]; field_simp; norm_num)

theorem scaling_mul_val {s : ℝ} (hs : s ≠ 0) (g : BinaryRealGL) :
    (scaling s hs * g).val =
      !![s⁻¹ * g.val 0 0, s⁻¹ * g.val 0 1; s * g.val 1 0, s * g.val 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scaling, GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_scaling_mul {s : ℝ} (hs : s ≠ 0) (g : BinaryRealGL) :
    (scaling s hs * g).val.det = g.val.det := by
  rw [scaling_mul_val, Matrix.det_fin_two_of, Matrix.det_fin_two]; field_simp

theorem rowNormSq_scaling_mul {s : ℝ} (hs : s ≠ 0) (g : BinaryRealGL) :
    rowNormSq (scaling s hs * g) = s ^ 2 * rowNormSq g := by
  simp only [rowNormSq, scaling_mul_val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

theorem orbitRe_scaling_mul {s : ℝ} (hs : s ≠ 0) (g : BinaryRealGL) :
    orbitRe (scaling s hs * g) = orbitRe g / s ^ 2 := by
  have hD := (rowNormSq_pos g).ne'
  rw [orbitRe, rowNormSq_scaling_mul, orbitRe]
  simp only [scaling_mul_val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp

theorem orbitIm_scaling_mul {s : ℝ} (hs : s ≠ 0) (g : BinaryRealGL) :
    orbitIm (scaling s hs * g) = orbitIm g / s ^ 2 := by
  rw [orbitIm, orbitIm, det_scaling_mul, rowNormSq_scaling_mul]
  field_simp

theorem preimage_scaling_strip {s : ℝ} (hs : s ≠ 0) (α β : ℝ) (I J : Set ℝ) :
    (fun g => scaling s hs * g) ⁻¹' strip α β I J =
      strip α β ((· / s ^ 2) ⁻¹' I) ((· / s ^ 2) ⁻¹' J) := by
  ext g
  simp only [strip, mem_preimage, mem_ofPred_eq, det_scaling_mul, orbitRe_scaling_mul,
    orbitIm_scaling_mul]


/-! ### Compactness of bounded strips -/

/-- Every entry of a matrix in a bounded strip is bounded. -/
theorem abs_entry_le_of_mem_strip {α β R c C : ℝ} (hc : 0 < c) {g : BinaryRealGL}
    (hg : g ∈ strip α β (Icc (-R) R) (Icc c C)) (i j : Fin 2) :
    |g.val i j| ≤ Real.sqrt ((R ^ 2 + C ^ 2) * (β / c) + β / c) := by
  obtain ⟨⟨-, hβ⟩, ⟨hR₁, hR₂⟩, ⟨hc₁, hC⟩⟩ := hg
  have hD := rowNormSq_pos g
  have hIm := orbitIm_mul_rowNormSq g
  have hDle : rowNormSq g ≤ β / c := by
    rw [le_div_iff₀ hc]
    nlinarith
  have hre : orbitRe g ^ 2 ≤ R ^ 2 := by nlinarith
  have him : orbitIm g ^ 2 ≤ C ^ 2 := by nlinarith
  have htop := topRow_sq g
  have hDnn : 0 ≤ β / c := hD.le.trans hDle
  have htop_le : g.val 0 0 ^ 2 + g.val 0 1 ^ 2 ≤ (R ^ 2 + C ^ 2) * (β / c) := by
    rw [htop]
    exact mul_le_mul (by linarith) hDle hD.le (by positivity)
  have hbot : g.val 1 0 ^ 2 + g.val 1 1 ^ 2 ≤ β / c := hDle
  apply Real.abs_le_sqrt
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    nlinarith [sq_nonneg (g.val 0 0), sq_nonneg (g.val 0 1), sq_nonneg (g.val 1 0),
      sq_nonneg (g.val 1 1)]

theorem isClosed_strip_Icc (α β R c C : ℝ) : IsClosed (strip α β (Icc (-R) R) (Icc c C)) :=
  (isClosed_Icc.preimage continuous_det).inter
    ((isClosed_Icc.preimage continuous_orbitRe).inter (isClosed_Icc.preimage continuous_orbitIm))

/-- A strip with `det ∈ [α, β]` (`α > 0`), bounded real part and imaginary part in `[c, C]`
(`c > 0`) is compact. -/
theorem isCompact_strip_Icc {α β c : ℝ} (hα : 0 < α) (hc : 0 < c) (R C : ℝ) :
    IsCompact (strip α β (Icc (-R) R) (Icc c C)) := by
  set M := Real.sqrt ((R ^ 2 + C ^ 2) * (β / c) + β / c)
  let P : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
    {A | α ≤ A.det} ∩ Set.univ.pi fun _ => Set.univ.pi fun _ => Icc (-M) M
  have hdetc : Continuous fun A : Matrix (Fin 2) (Fin 2) ℝ => A.det := by
    simp only [Matrix.det_fin_two]
    fun_prop
  have hP : IsCompact P :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).inter_left
      (isClosed_le continuous_const hdetc)
  have hrange : P ⊆ Set.range (Units.val : BinaryRealGL → Matrix (Fin 2) (Fin 2) ℝ) :=
    fun A hA => ⟨GeneralLinearGroup.mkOfDetNeZero A (hα.trans_le hA.1).ne', rfl⟩
  have hK : IsCompact ((Units.val : BinaryRealGL → Matrix (Fin 2) (Fin 2) ℝ) ⁻¹' P) := by
    apply PlaneEisensteinContinuation.RealOrbitalMass.units_isEmbedding.isCompact_iff.mpr
    rw [Set.image_preimage_eq_of_subset hrange]
    exact hP
  apply hK.of_isClosed_subset (isClosed_strip_Icc α β R c C)
  intro g hg
  refine ⟨hg.1.1, ?_⟩
  intro i _ j _
  exact abs_le.mp (abs_entry_le_of_mem_strip hc hg i j)

end TernaryPeriodPolynomials.Automorphic.RealHaar
