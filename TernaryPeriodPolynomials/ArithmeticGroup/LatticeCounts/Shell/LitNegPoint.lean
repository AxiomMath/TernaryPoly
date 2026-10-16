module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitTotal
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitNegConj
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitNegK0

@[expose] public section


/-!
# The literal integrand on the negative-determinant branch, pointwise

For `det g∞ < 0` and every `z ∈ ℚ_p²`, the literal integrand satisfies
`shellIntegrand g∞ z = shellIntegrand (R g∞) (z.1, -z.2)`, where `R = diag(1,-1)`.
Take a K0 block `(r, k, A)` of `z`. Both sides are `c(r)` times a value of `v_h`, and the value at
`g∞` is the reflected value at `R g∞` with the conjugated block `diag(1,-1) A diag(1,-1)`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix PadicInt
open TernaryPeriodPolynomials.SourceConstruction (EichlerInput)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (finiteCompletionPadicEquiv cuspScalarWeightedLinear)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
  (reflectionGL reflectionQ det_reflectionQ_real vhValueFull)
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
  (binaryRationalReal binaryRationalFinite)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation (ιGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegK0 (dD K0Spec_neg)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegConj
  (vhValueNeg_eq_conj conj_ιGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0 (K0Spec)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL (psiV finiteCompletionPadicEquiv_psiV)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegPoint

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- Every point of `ℚ_p²` has a K0 block at some level `r`. -/
theorem exists_block {p : ℕ} [Fact p.Prime] (z : ℚ_[p] × ℚ_[p]) :
    ∃ (r : ℕ) (k : Matrix (Fin 3) (Fin 3) ℤ_[p]) (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
      K0Spec r z.1 z.2 k A := by
  rcases ShellLitTotal.zp2_or_shell z with hz | ⟨r, hr⟩
  · obtain ⟨k, hK⟩ := ShellLitZp2.exists_k0_integral (s := z.1) (t := z.2) hz.1 hz.2
    exact ⟨0, k, 1, hK⟩
  · obtain ⟨k, A, hK⟩ := SeedK0.exists_k0 (r + 1) (s := z.1) (t := z.2)
      (show max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ (r + 1) from hr)
    exact ⟨r + 1, k, A, hK⟩

section Point

variable (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]

/-- The integral block `A` with its entries mapped into `K_v` by `ψ_v`. -/
def blockMat (A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
  A.map (ShellLitBasis.psiInt v)

theorem psiInt_ne_zero {x : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]} (hx : x ≠ 0) :
    ShellLitBasis.psiInt v x ≠ 0 := by
  intro h0
  apply hx
  have h1 := congrArg (finiteCompletionPadicEquiv v) h0
  rw [show ShellLitBasis.psiInt v x = psiV v ((x : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) from rfl,
    finiteCompletionPadicEquiv_psiV, map_zero] at h1
  exact PadicInt.coe_eq_zero.1 h1

theorem blockMat_det_ne {A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hA : A.det ≠ 0) : (blockMat v A).det ≠ 0 := by
  have h1 : ShellLitBasis.psiInt v A.det = (blockMat v A).det :=
    RingHom.map_det (ShellLitBasis.psiInt v) A
  rw [← h1]
  exact psiInt_ne_zero v hA

/-- The integral block as an element of `GL₂(K_v)`. -/
def blockGL {A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hA : A.det ≠ 0) : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (blockMat v A) (blockMat_det_ne v hA)

theorem blockGL_val {A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hA : A.det ≠ 0) (i j : Fin 2) :
    (blockGL v hA).val i j = (finiteCompletionPadicEquiv v).symm
      (((A i j : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])) := rfl

theorem refl_map : (dD.map (ShellLitBasis.psiInt v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
    (reflectionGL (v.adicCompletion ℚ)).val := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dD, reflectionGL, ShellLitBasis.psiInt]

theorem reflect_blockGL {A : Matrix (Fin 2) (Fin 2) ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val]}
    (hA : A.det ≠ 0) :
    (reflectionGL (v.adicCompletion ℚ) * blockGL v hA * reflectionGL (v.adicCompletion ℚ)).val =
      blockMat v (dD * A * dD) := by
  rw [Units.val_mul, Units.val_mul]
  show (reflectionGL (v.adicCompletion ℚ)).val * blockMat v A *
    (reflectionGL (v.adicCompletion ℚ)).val = blockMat v (dD * A * dD)
  rw [← refl_map v]
  unfold blockMat
  rw [Matrix.map_mul, Matrix.map_mul]

/-- **Pointwise identity on the negative branch.** For `det g∞ < 0`, the literal integrand at `z`
equals the literal integrand at `R g∞` and at `(z.1, -z.2)`. -/
theorem shellIntegrand_neg (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hgInf : (Matrix.GeneralLinearGroup.det gInf).val < 0)
    (z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
    ShellLitFibre.shellIntegrand v I gInf z =
      ShellLitFibre.shellIntegrand v I (binaryRationalReal reflectionQ * gInf) (z.1, -z.2) := by
  obtain ⟨r, k, A, hK⟩ := exists_block z
  have hpne : ((Rat.HeightOneSpectrum.primesEquiv v).val : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v).val])
      ≠ 0 := by
    exact_mod_cast (Fact.out : (Rat.HeightOneSpectrum.primesEquiv v).val.Prime).ne_zero
  have hdet : A.det ≠ 0 := by
    obtain ⟨-, hA0, -⟩ := hK
    rw [hA0]
    exact pow_ne_zero _ hpne
  have hK' := K0Spec_neg hK
  have hRg : 0 < (Matrix.GeneralLinearGroup.det (binaryRationalReal reflectionQ * gInf)).val := by
    simp only [map_mul, Units.val_mul, det_reflectionQ_real]
    linarith
  have L := ShellLitPlane.integrand_eq_vhValueFull v I h hform gInf (r := r) (z := z) hK
    (blockGL v hdet) (blockGL_val v hdet)
  have R := ShellLitPlane.integrand_eq_vhValueFull v I h hform (binaryRationalReal reflectionQ * gInf)
    (r := r) (z := (z.1, -z.2)) hK'
    (reflectionGL (v.adicCompletion ℚ) * blockGL v hdet * reflectionGL (v.adicCompletion ℚ))
    (fun i j => by rw [reflect_blockGL v hdet]; rfl)
  unfold ShellLitFibre.shellIntegrand
  rw [L, R]
  congr 1
  rw [vhValueFull, vhValueFull, ite_eq_right (not_lt.2 hgInf.le), ite_eq_left hRg,
    vhValueNeg_eq_conj _ h gInf hgInf (ιGL v (blockGL v hdet)), conj_ιGL v (blockGL v hdet)]

end Point

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegPoint
