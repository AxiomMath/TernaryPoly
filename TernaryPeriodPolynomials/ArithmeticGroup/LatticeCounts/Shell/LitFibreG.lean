module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitBasis
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitPlane
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitDetNorm
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.SeedK0
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.IotaValue
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.PermZp
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Coset
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.ReductionProof

@[expose] public section


/-!
# Fibre constancy of the literal shell integrand at a general base point (`g_f`)

Formalized by Claude Haiku 5.5.

Generalises `ShellLitFibre` (base point `g_f = 1`) to an arbitrary finite base point `g_f`.
The base point enters through `gf : BinaryFiniteGL` and `gp : GL₂(K_v)` with
`gf.val.map (finiteEvaluation v) = gp.val` and `IntGL v gp.val` (the "integral at `v`" hypothesis).
The integrand is `smoothReal` of the plane section of `ι₃(L z) · blk(g_f)`, and the fibre value is
`p^{-s·k/2} · normPower(det g_f) · vhValueFull k h g∞ (ι_v B · (g_f · ι_v gp⁻¹))`, constant on the
fibre of the Hermite triple `t`.

Ingredients: the general model identity `vhModel_eq_full_gen` (any `X : BinaryFiniteGL`); the
commutation `ι_v U · Y = Y · ι_v U` for `Y` trivial at `v`; right-invariance of `vhValueFull` under
integral factors, applied after moving `ι_v g` past `Y`.
-/

open Matrix PadicInt MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL
open TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSection
open TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSpecialize
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitDetNorm
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue
  (vhValue_eq_of_reduction)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof
  (latticeReductionExists evM)
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0 (exists_k0 K0Spec)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (cuspScalarWeightedLinear finiteCompletionPadicEquiv)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBasis
  (psiInt exists_mul_Mz ιGL_mem_bIF ιGL_mul')
open TernaryPeriodPolynomials.Argument.LatticeCounts.Padic (pairShell pairLat hermLat)
open TernaryPeriodPolynomials.Argument.LatticeCounts.IotaValue (intMat)
open TernaryPeriodPolynomials.Argument.LatticeCounts (cyclicHNF hnfData mem_hnfData)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibreG

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The adic completion of `ℚ` at a finite place has characteristic zero (as in `ShellLitFibre`). -/
instance charZero_adicCompletion_fin (v : FinitePlace) : CharZero (v.adicCompletion ℚ) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective

section Model

/-- **The model identity at an arbitrary finite element.** Same proof as `vhModel_eq_full`, with
the lattice reduction of `X` in place of that of `ι_p A`. -/
theorem vhModel_eq_full_gen (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (X : BinaryFiniteGL) (gInf : BinaryRealGL) :
    smoothReal σ (σ.π (atFinite X) I.vector.val) (atInfinity gInf) =
      vhValueFull (-2 * I.halfWeight) h gInf X := by
  unfold vhValueFull
  by_cases hpos : 0 < (GeneralLinearGroup.det gInf).val
  · rw [ite_eq_left hpos, vhValue_eq_of_reduction (-2 * I.halfWeight) h gInf hpos X
      (Classical.choice (latticeReductionExists X))]
    exact vhModel_realize_eq_of_reduction I h hform gInf hpos X _
  · have hneg : (GeneralLinearGroup.det gInf).val < 0 :=
      lt_of_le_of_ne (not_lt.mp hpos) (GeneralLinearGroup.det gInf).ne_zero
    rw [ite_eq_right hpos, vhValueNeg_eq_of_reduction (-2 * I.halfWeight) h gInf hneg X
      (Classical.choice (latticeReductionExists X))]
    exact vhModel_eq_neg_of_reduction I h hform gInf hneg X _

end Model

section Trivial

/-- `Y = g_f · ι_v(gp⁻¹)` is the identity at the place `v` when `g_f` reduces to `gp` at `v`. -/
theorem trivial_at_v (v : FinitePlace) (gf : BinaryFiniteGL)
    (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) :
    (gf * ιGL v gp⁻¹).val.map (finiteEvaluation v) = 1 := by
  rw [Units.val_mul, ιGL_val, Matrix.map_mul]
  have h2 : (ιMat v (gp⁻¹).val).map (finiteEvaluation v) = (gp⁻¹).val := evM_ιMat_self v _
  rw [h2, hgp, ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one]

/-- `ι_v(U)` commutes with every `Y` that is the identity at `v`: they act on disjoint places. -/
theorem ιGL_comm_of_trivial (v : FinitePlace)
    (U : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (Y : BinaryFiniteGL) (hY : Y.val.map (finiteEvaluation v) = 1) :
    ιGL v U * Y = Y * ιGL v U := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ιGL_val]
  apply ext_of_evM
  intro w
  have hL : evM w (ιMat v U.val * Y.val) = evM w (ιMat v U.val) * evM w Y.val := by
    unfold evM
    exact Matrix.map_mul
  have hR : evM w (Y.val * ιMat v U.val) = evM w Y.val * evM w (ιMat v U.val) := by
    unfold evM
    exact Matrix.map_mul
  rw [hL, hR]
  by_cases hw : w = v
  · rw [hw]
    have hYv : evM v Y.val = 1 := hY
    rw [evM_ιMat_self, hYv, mul_one, one_mul]
  · rw [evM_ιMat_ne v w hw, mul_one, one_mul]

end Trivial

section Factor

/-- **Right-invariance with a trailing factor `Y` trivial at `v`.** Replacing the block `B₁` by
`B₂` (with `B₁ = B₂ · U` for an integral `U` of determinant `1`) does not change
`vhValueFull (ι_v B · Y)`. -/
theorem vhValueFull_of_factor_G (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (k : ℤ)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne k)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (A₁ A₂ U : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val])
    (hU : U.det = 1) (hAU : A₁ = A₂ * U)
    (B₁ B₂ : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB₁ : ∀ i j, B₁.val i j = psiInt v (A₁ i j))
    (hB₂ : ∀ i j, B₂.val i j = psiInt v (A₂ i j))
    (Y : BinaryFiniteGL) (hY : Y.val.map (finiteEvaluation v) = 1) :
    vhValueFull k h gInf (ιGL v B₁ * Y) = vhValueFull k h gInf (ιGL v B₂ * Y) := by
  obtain ⟨g, hgv, hgmem⟩ := ιGL_mem_bIF v U hU
  have hblk : B₁ = B₂ * g := by
    apply Units.ext
    rw [Units.val_mul, hgv]
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, hB₁, hB₂, hAU, map_sum, map_mul]
  rw [hblk, ιGL_mul' v, mul_assoc, ιGL_comm_of_trivial v g Y hY, ← mul_assoc]
  unfold vhValueFull
  rw [ite_eq_left hg, ite_eq_left hg, vhValue_mul_integral k h gInf hg (ιGL v B₂ * Y) (ιGL v g) hgmem]

end Factor

section Integrand

/-- The literal shell integrand at a general base point `g_f`: the smooth-vector value at the
plane section of `ι₃(L z) · blk(g_f)`, with `b = k/2`, `k = -2·halfWeight`, at `g∞`. -/
def shellIntegrandG (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n) (gf : BinaryFiniteGL) (gInf : BinaryRealGL)
    (z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) : ℂ :=
  smoothReal σ (finitePlaneVector σ GeneralEisenstein.trivialCharacter 0
    (((-2 * I.halfWeight : ℤ) : ℂ) / 2) (ιGL3 v (LstV v z) * blkGL gf) I.vector.val)
    (atInfinity gInf)

/-- **Integrand at a general base point, in block form.** -/
theorem shellIntegrandG_eq_block (v : FinitePlace)
    [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) {r : ℕ} {z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {k : Matrix (Fin 3) (Fin 3) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    {A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hK : K0Spec r z.1 z.2 k A)
    (Ablk : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hA : ∀ i j, Ablk.val i j = (finiteCompletionPadicEquiv v).symm
      (((A i j : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])))
    (gf : BinaryFiniteGL) (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) (hgI : IntGL v gp.val) :
    shellIntegrandG v I gf gInf z =
      ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(r : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) : ℝ) : ℂ) *
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
          (((-2 * I.halfWeight : ℤ) : ℂ) / 2) *
        vhValueFull (-2 * I.halfWeight) h gInf (ιGL v Ablk * (gf * ιGL v gp⁻¹)) := by
  have hsph : I.vector.val ∈ sphericalSubspace σ := fun kk => I.vector_spherical kk
  unfold shellIntegrandG
  rw [finitePlaneVector_blk_iota_LstV_det v hK Ablk hA _ hsph gf gp hgp hgI,
    ShellLitPlane.smoothReal_smul_of_mem σ _ (σ.smooth_stable _ _ I.vector.property),
    ShellLitPlane.exp_shell_eq_rpow (Rat.HeightOneSpectrum.primesEquiv v).val r
      (-2 * I.halfWeight),
    vhModel_eq_full_gen I h hform, smul_eq_mul]

/-- **Fibre constancy at a general base point.** On the fibre of `t`, the literal integrand is
`p^{-s·k/2} · normPower(det g_f) · vhValueFull k h g∞ (ι_v B · (g_f · ι_v gp⁻¹))` for any block `B`
of `Mz t`. The factor `normPower(det g_f)` does not depend on `z`. -/
theorem shellIntegrandG_fibre (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (gf : BinaryFiniteGL) (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) (hgI : IntGL v gp.val)
    {s : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicHNF (Rat.HeightOneSpectrum.primesEquiv v).val s)
    {z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hz : z ∈ pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s)
    (hzt : pairLat (Rat.HeightOneSpectrum.primesEquiv v).val z =
      hermLat (Rat.HeightOneSpectrum.primesEquiv v).val t)
    (B : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : ∀ i j, B.val i j = psiInt v
      (LatticePermZp.Mz (q := (Rat.HeightOneSpectrum.primesEquiv v).val) t i j)) :
    shellIntegrandG v I gf gInf z =
      ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) : ℝ) : ℂ) *
        normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det gf))
          (((-2 * I.halfWeight : ℤ) : ℂ) / 2) *
        vhValueFull (-2 * I.halfWeight) h gInf (ιGL v B * (gf * ιGL v gp⁻¹)) := by
  obtain ⟨k, A, hK⟩ := exists_k0 s
    (show max ‖z.1‖ ‖z.2‖ = ((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^ s from hz)
  have hdet : A.det = ((Rat.HeightOneSpectrum.primesEquiv v).val :
      ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) ^ s := hK.2.1
  have hA0 := hK.2.2.1
  have hdetmap : (A.map (psiInt v)).det = psiInt v A.det := by
    rw [RingHom.map_det]
    rfl
  have hunit : IsUnit (A.map (psiInt v)).det := by
    rw [hdetmap, hdet, map_pow, map_natCast, isUnit_iff_ne_zero]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Rat.HeightOneSpectrum.primesEquiv v).property.ne_zero)
  let Ablk := Matrix.nonsingInvUnit (A.map (psiInt v)) hunit
  have hAblk : ∀ i j, Ablk.val i j = (finiteCompletionPadicEquiv v).symm
      (((A i j : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])) := fun i j => rfl
  have hint := shellIntegrandG_eq_block v I h hform gInf hK Ablk hAblk gf gp hgp hgI
  obtain ⟨D, hAD, hD⟩ := exists_mul_Mz ht hzt hdet hA0
  have hY := trivial_at_v v gf gp hgp
  have hfac := vhValueFull_of_factor_G v (-2 * I.halfWeight) h gInf hg A
    (LatticePermZp.Mz (q := (Rat.HeightOneSpectrum.primesEquiv v).val) t) D hD hAD Ablk B
    (fun i j => rfl) hB (gf * ιGL v gp⁻¹) hY
  rw [hint, hfac]

end Integrand

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibreG

end
