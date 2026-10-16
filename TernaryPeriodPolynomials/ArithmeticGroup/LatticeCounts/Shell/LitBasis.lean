module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitPlane
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.PermZp
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LtDictionary
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Coset
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.IotaValue
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.FiniteReduction

@[expose] public section


/-!
# Basis change for the literal shell integrand (part 3c)

If `pairLat z = hermLat t` for a cyclic Hermite triple `t` of level `p^r`, and `A` is a `K0Spec`
block of `z`, then `A = Mz t · D` with `det D = 1` (`exists_mul_Mz`). Two blocks `A₁, A₂` of the
same lattice differ by a right factor `U = adj D₂ · D₁` of determinant one (`block_factor`). Its
image in `GL₂(K_v)` lies in `binaryIntegralFinite`, so `vhValue` is unchanged
(`vhValue_mul_integral`). Hence `vhValueFull k h g∞ (ι_v A)` depends only on the triple `t`
(`vhValueFull_same_lattice`).

Formalized by Claude Haiku 5.5.
-/

open PadicInt Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermZp (Mz mulLin coord_of_range Mz_det)
open TernaryPeriodPolynomials.Argument.LatticeCounts.Padic (pairLat hermLat)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic (OS mem_iff_norm intGL_one)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
  (ιGL ιMat ιMat_mul ιGL_val evM_ιMat_self evM_ιMat_ne vhValue_mul_integral)
open TernaryPeriodPolynomials.Argument.LatticeCounts.IotaValue (mem_binaryIntegralFinite_of_intGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction (binaryIntegralFinite)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg (vhValueFull)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL (psiV finiteCompletionPadicEquiv_psiV)
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0 (K0Spec)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (finiteCompletionPadicEquiv)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBasis

section Lattice

variable {p : ℕ} [Fact p.Prime]

/-- `det Mz t = p^r` for a cyclic Hermite triple of level `p^r`. -/
theorem Mz_det_eq_pow {r : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicHNF p r) :
    (Mz (q := p) t).det = (p : ℤ_[p]) ^ r := by
  have hn : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos r
  have h := ((mem_hnfData hn t).1 (Finset.mem_filter.mp ht).1).2.1
  rw [Mz_det, h, Nat.cast_pow]

/-- Each column of a `K0Spec` block lies in `hermLat t`, once `pairLat z = hermLat t`. -/
theorem col_mem_hermLat {t : ℕ × ℕ × ℕ} {z : ℚ_[p] × ℚ_[p]} (hz : pairLat p z = hermLat p t)
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hA : ∀ j : Fin 2, ‖z.1 * (A 0 j : ℚ_[p]) + z.2 * (A 1 j : ℚ_[p])‖ ≤ 1) (j : Fin 2) :
    ((A 0 j, A 1 j) : ℤ_[p] × ℤ_[p]) ∈ LinearMap.range (mulLin (Mz (q := p) t)) := by
  have hmem : ((A 0 j, A 1 j) : ℤ_[p] × ℤ_[p]) ∈ pairLat p z := hA j
  rw [hz] at hmem
  exact hmem

/-- Factorisation `A = Mz t · D` with `det D = 1` for a block of a lattice `pairLat z = hermLat t`. -/
theorem exists_mul_Mz {r : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicHNF p r)
    {z : ℚ_[p] × ℚ_[p]} (hz : pairLat p z = hermLat p t)
    {A : Matrix (Fin 2) (Fin 2) ℤ_[p]} (hdet : A.det = (p : ℤ_[p]) ^ r)
    (hA : ∀ j : Fin 2, ‖z.1 * (A 0 j : ℚ_[p]) + z.2 * (A 1 j : ℚ_[p])‖ ≤ 1) :
    ∃ D : Matrix (Fin 2) (Fin 2) ℤ_[p], A = Mz (q := p) t * D ∧ D.det = 1 := by
  have hcols : ∀ j : Fin 2, ∃ c : Fin 2 → ℤ_[p], ∀ i : Fin 2,
      A i j = ∑ k, Mz (q := p) t i k * c k := by
    intro j
    obtain ⟨c, hc⟩ := coord_of_range (Mz (q := p) t) (A 0 j, A 1 j) (col_mem_hermLat hz A hA j)
    refine ⟨c, fun i => ?_⟩
    have h := hc i
    fin_cases i <;> simpa using h
  choose c hc using hcols
  refine ⟨Matrix.of fun k j => c j k, ?_, ?_⟩
  · ext i j
    rw [hc j i]
    simp [Matrix.mul_apply]
  · have hAD : A = Mz (q := p) t * Matrix.of fun k j => c j k := by
      ext i j
      rw [hc j i]
      simp [Matrix.mul_apply]
    have hd : A.det = (Mz (q := p) t).det * (Matrix.of fun k j => c j k).det := by
      rw [← Matrix.det_mul, ← hAD]
    rw [Mz_det_eq_pow ht, hdet] at hd
    have hne : (p : ℤ_[p]) ^ r ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    exact mul_left_cancel₀ hne (by rw [mul_one]; exact hd.symm)

/-- Two blocks of the same lattice differ by an integral right factor of determinant one. -/
theorem block_factor {r : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicHNF p r)
    {z₁ z₂ : ℚ_[p] × ℚ_[p]} (hz₁ : pairLat p z₁ = hermLat p t) (hz₂ : pairLat p z₂ = hermLat p t)
    {A₁ A₂ : Matrix (Fin 2) (Fin 2) ℤ_[p]} (hd₁ : A₁.det = (p : ℤ_[p]) ^ r)
    (hd₂ : A₂.det = (p : ℤ_[p]) ^ r)
    (hA₁ : ∀ j : Fin 2, ‖z₁.1 * (A₁ 0 j : ℚ_[p]) + z₁.2 * (A₁ 1 j : ℚ_[p])‖ ≤ 1)
    (hA₂ : ∀ j : Fin 2, ‖z₂.1 * (A₂ 0 j : ℚ_[p]) + z₂.2 * (A₂ 1 j : ℚ_[p])‖ ≤ 1) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℤ_[p], A₁ = A₂ * U ∧ U.det = 1 := by
  obtain ⟨D₁, h₁, hD₁⟩ := exists_mul_Mz ht hz₁ hd₁ hA₁
  obtain ⟨D₂, h₂, hD₂⟩ := exists_mul_Mz ht hz₂ hd₂ hA₂
  have hinv : D₂ * D₂.adjugate = 1 := by rw [Matrix.mul_adjugate, hD₂, one_smul]
  refine ⟨D₂.adjugate * D₁, ?_, ?_⟩
  · rw [h₁, h₂, Matrix.mul_assoc, ← Matrix.mul_assoc D₂, hinv, Matrix.one_mul]
  · simp [Matrix.det_mul, Matrix.det_adjugate, hD₁, hD₂]

end Lattice

section Lift

variable (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]

/-- The ring map `ℤ_p → K_v`, `x ↦ ψ_v(x)`, where `ℤ_p ⊂ ℚ_p`. -/
def psiInt : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val] →+* v.adicCompletion ℚ :=
  (psiV v).comp PadicInt.Coe.ringHom

theorem norm_psiInt (x : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
    ‖finiteCompletionPadicEquiv v (psiInt v x)‖ ≤ 1 := by
  show ‖finiteCompletionPadicEquiv v (psiV v (x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]))‖ ≤ 1
  rw [finiteCompletionPadicEquiv_psiV]
  exact PadicInt.norm_le_one _

/-- An integral `GL₂(ℤ_p)` element, placed in `GL₂(K_v)`, has `ι_v` in `binaryIntegralFinite`. -/
theorem ιGL_mem_bIF (U : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val])
    (hU : U.det = 1) :
    ∃ g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ),
      g.val = U.map (psiInt v) ∧ ιGL v g ∈ binaryIntegralFinite := by
  have h1 : U * U.adjugate = 1 := by rw [Matrix.mul_adjugate, hU, one_smul]
  have h2 : U.adjugate * U = 1 := by rw [Matrix.adjugate_mul, hU, one_smul]
  have hX : U.map (psiInt v) * U.adjugate.map (psiInt v) = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one (psiInt v) (map_zero _) (map_one _)]
  have hY : U.adjugate.map (psiInt v) * U.map (psiInt v) = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one (psiInt v) (map_zero _) (map_one _)]
  let g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) :=
    ⟨U.map (psiInt v), U.adjugate.map (psiInt v), hX, hY⟩
  have hinv : (U.map (psiInt v))⁻¹ = U.adjugate.map (psiInt v) := Matrix.inv_eq_right_inv hX
  refine ⟨g, rfl, ?_⟩
  apply mem_binaryIntegralFinite_of_intGL
  intro w
  rw [ιGL_val]
  by_cases hw : w = v
  · rw [hw, evM_ιMat_self]
    refine ⟨Matrix.isUnit_det_of_right_inverse hX, fun i j => (mem_iff_norm v _).2 (norm_psiInt v _), ?_⟩
    intro i j
    rw [show (g.val)⁻¹ = U.adjugate.map (psiInt v) from hinv]
    exact (mem_iff_norm v _).2 (norm_psiInt v _)
  · rw [evM_ιMat_ne v w hw]
    exact intGL_one w

omit [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime] in
/-- `ι_v` is multiplicative on `GL₂`. -/
theorem ιGL_mul' (A B : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    ιGL v (A * B) = ιGL v A * ιGL v B := by
  apply Units.ext
  simp only [ιGL_val, Units.val_mul, ιMat_mul]

/-- Replacing a block by an integral right translate does not change `vhValueFull`. -/
theorem vhValueFull_of_factor (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (A₁ A₂ U : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val])
    (hU : U.det = 1) (hAU : A₁ = A₂ * U)
    (B₁ B₂ : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB₁ : ∀ i j, B₁.val i j = psiInt v (A₁ i j))
    (hB₂ : ∀ i j, B₂.val i j = psiInt v (A₂ i j)) :
    vhValueFull k h gInf (ιGL v B₁) = vhValueFull k h gInf (ιGL v B₂) := by
  obtain ⟨g, hgv, hgmem⟩ := ιGL_mem_bIF v U hU
  have hblk : B₁ = B₂ * g := by
    apply Units.ext
    rw [Units.val_mul, hgv]
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, hB₁, hB₂, hAU, map_sum, map_mul]
  rw [hblk, ιGL_mul' v]
  unfold vhValueFull
  rw [ite_eq_left hg, ite_eq_left hg, vhValue_mul_integral k h gInf hg (ιGL v B₂) (ιGL v g) hgmem]

/-- **The block value depends only on the Hermite triple.** For two `K0Spec`-type blocks of
lattices `pairLat z = hermLat t` with the same `t`, the values `vhValueFull` at `ι_v` agree. -/
theorem vhValueFull_same_lattice (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    {r : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicHNF (Rat.HeightOneSpectrum.primesEquiv v).val r)
    {z₁ z₂ : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hz₁ : pairLat (Rat.HeightOneSpectrum.primesEquiv v).val z₁ =
      hermLat (Rat.HeightOneSpectrum.primesEquiv v).val t)
    (hz₂ : pairLat (Rat.HeightOneSpectrum.primesEquiv v).val z₂ =
      hermLat (Rat.HeightOneSpectrum.primesEquiv v).val t)
    {A₁ A₂ : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hd₁ : A₁.det = ((Rat.HeightOneSpectrum.primesEquiv v).val : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) ^ r)
    (hd₂ : A₂.det = ((Rat.HeightOneSpectrum.primesEquiv v).val : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) ^ r)
    (hA₁ : ∀ j : Fin 2, ‖z₁.1 * (A₁ 0 j : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) +
      z₁.2 * (A₁ 1 j : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])‖ ≤ 1)
    (hA₂ : ∀ j : Fin 2, ‖z₂.1 * (A₂ 0 j : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) +
      z₂.2 * (A₂ 1 j : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])‖ ≤ 1)
    (B₁ B₂ : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB₁ : ∀ i j, B₁.val i j = psiInt v (A₁ i j))
    (hB₂ : ∀ i j, B₂.val i j = psiInt v (A₂ i j)) :
    vhValueFull k h gInf (ιGL v B₁) = vhValueFull k h gInf (ιGL v B₂) := by
  obtain ⟨U, hAU, hU⟩ := block_factor ht hz₁ hz₂ hd₁ hd₂ hA₁ hA₂
  exact vhValueFull_of_factor v k h gInf hg A₁ A₂ U hU hAU B₁ B₂ hB₁ hB₂

end Lift

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBasis

end
