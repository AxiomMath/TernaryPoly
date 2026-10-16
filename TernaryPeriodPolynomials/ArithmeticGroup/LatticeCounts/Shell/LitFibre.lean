module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitBasis
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitPlane
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.SeedK0
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.IotaValue
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.PermZp
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Coset

@[expose] public section


/-!
# Fibre constancy of the literal shell integrand

Formalized by Claude Haiku 5.5.

`shellIntegrand v I g∞ z` is the literal integrand: the plane section of the smooth vector at
`ι_v(L(z))`. For `z` in the shell of valuation `s` with `pairLat z = hermLat t`, it equals
`p^{-s·k/2} · vhValue k h g∞ (ι_v B)` for any block `B` with `B.val = (Mz t).map ψ`, where
`k = -2·halfWeight`. The block `shellB v t` is the integer matrix `intMat t` in `GL₂(K_v)`.
-/

open Matrix PadicInt MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation (ιGL)
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers (cuspScalarWeightedLinear)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL
open TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSection
open TernaryPeriodPolynomials.Argument.LatticeCounts.PlaneSpecialize
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0 (exists_k0 K0Spec)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (finiteCompletionPadicEquiv)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBasis
  (psiInt exists_mul_Mz vhValueFull_of_factor)
open TernaryPeriodPolynomials.Argument.LatticeCounts.Padic (pairShell pairLat hermLat)
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue (vhValue)
open TernaryPeriodPolynomials.Argument.LatticeCounts.IotaValue (intMat)
open TernaryPeriodPolynomials.Argument.LatticeCounts (cyclicHNF hnfData mem_hnfData)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibre

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The literal shell integrand at `z`: the smooth-vector value at the plane section of
`ι_v(L(z))`, with the spherical-trivial character, `b = k/2`, `k = -2·halfWeight`, at `g∞`. -/
def shellIntegrand (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n) (gInf : BinaryRealGL)
    (z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) : ℂ :=
  smoothReal σ (finitePlaneVector σ GeneralEisenstein.trivialCharacter 0
    (((-2 * I.halfWeight : ℤ) : ℂ) / 2) (ιGL3 v (LstV v z)) I.vector.val) (atInfinity gInf)

/-- The adic completion of `ℚ` at a finite place has characteristic zero (it is a `ℚ`-algebra
that is a field). -/
instance charZero_adicCompletion_fin (v : FinitePlace) : CharZero (v.adicCompletion ℚ) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective

open Classical in
/-- The block of a Hermite triple: the integer matrix `intMat t` in `GL₂(K_v)`. -/
def shellB (v : FinitePlace) (t : ℕ × ℕ × ℕ) : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) :=
  if h : IsUnit ((intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ)).det then
    Matrix.nonsingInvUnit _ h
  else 1

theorem isUnit_det_intMat (v : FinitePlace) {s : ℕ} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ hnfData ((Rat.HeightOneSpectrum.primesEquiv v).val ^ s)) :
    IsUnit ((intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ)).det := by
  have hpos : 0 < (Rat.HeightOneSpectrum.primesEquiv v).val ^ s :=
    pow_pos (Rat.HeightOneSpectrum.primesEquiv v).property.pos s
  have hm := ((mem_hnfData hpos t).1 ht).2.1
  have hdet : ((intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ)).det =
      ((t.1 * t.2.2 : ℕ) : v.adicCompletion ℚ) := by
    rw [Matrix.det_fin_two]
    simp [intMat]
  rw [hdet, hm, isUnit_iff_ne_zero]
  exact Nat.cast_ne_zero.2 (pow_ne_zero _ (Rat.HeightOneSpectrum.primesEquiv v).property.ne_zero)

theorem shellB_val (v : FinitePlace) {s : ℕ} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ hnfData ((Rat.HeightOneSpectrum.primesEquiv v).val ^ s)) :
    (shellB v t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ) := by
  unfold shellB
  rw [dite_eq_left (isUnit_det_intMat v ht)]
  rfl

theorem shellB_entry (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    {s : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ hnfData ((Rat.HeightOneSpectrum.primesEquiv v).val ^ s))
    (i j : Fin 2) :
    (shellB v t).val i j = psiInt v
      (LatticePermZp.Mz (q := (Rat.HeightOneSpectrum.primesEquiv v).val) t i j) := by
  rw [shellB_val v ht]
  fin_cases i <;> fin_cases j <;> simp [LatticePermZp.Mz, intMat, psiInt]

/-- **Fibre constancy.** On the fibre of `t`, the literal integrand is the constant
`p^{-s·k/2} · vhValue k h g∞ (ι_v B)` for any block `B` of `Mz t`; here `k = -2·halfWeight`. -/
theorem shellIntegrand_fibre (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hg : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    {s : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicHNF (Rat.HeightOneSpectrum.primesEquiv v).val s)
    {z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hz : z ∈ pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s)
    (hzt : pairLat (Rat.HeightOneSpectrum.primesEquiv v).val z =
      hermLat (Rat.HeightOneSpectrum.primesEquiv v).val t)
    (B : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : ∀ i j, B.val i j = psiInt v
      (LatticePermZp.Mz (q := (Rat.HeightOneSpectrum.primesEquiv v).val) t i j)) :
    shellIntegrand v I gInf z =
      ((((Rat.HeightOneSpectrum.primesEquiv v).val : ℝ) ^
          (-(s : ℝ) * (((-2 * I.halfWeight : ℤ) : ℝ) / 2)) : ℝ) : ℂ) *
        vhValue (-2 * I.halfWeight) h gInf (ιGL v B) := by
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
  have hint := ShellLitPlane.integrand_eq_vhValueFull v I h hform gInf hK Ablk hAblk
  obtain ⟨D, hAD, hD⟩ := exists_mul_Mz ht hzt hdet hA0
  have hfac := vhValueFull_of_factor v (-2 * I.halfWeight) h gInf hg A
    (LatticePermZp.Mz (q := (Rat.HeightOneSpectrum.primesEquiv v).val) t) D hD hAD Ablk B
    (fun i j => rfl) hB
  unfold shellIntegrand
  rw [hint, hfac]
  unfold vhValueFull
  rw [ite_eq_left hg]

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibre
