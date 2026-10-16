module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitFibreG
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitNegPoint
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitNegConj
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitNegK0

@[expose] public section


/-!
# The literal integrand on the negative-determinant branch at a general base point (`g_f`)

Formalized by Claude Haiku 5.5.

Generalises `ShellLitNegPoint.shellIntegrand_neg` (base point `g_f = 1`) to an arbitrary finite base
point `g_f`, with `gf.val.map (finiteEvaluation v) = gp.val` and `IntGL v gp.val` as explicit hypotheses.
For `det g∞ < 0` and every `z ∈ ℚ_p²`:
`shellIntegrandG g_f g∞ z = shellIntegrandG (R g_f R) (R g∞) (z.1, -z.2)`, with `R = diag(1,-1)`
at both places. The reflected base point is integral at `v` with local component `R gp R`.
The normalising factor `normPower(det g_f) b` is unchanged, since `det (R g_f R) = det g_f`.
-/

open MeasureTheory Matrix PadicInt
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction (EichlerInput)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (finiteCompletionPadicEquiv cuspScalarWeightedLinear)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
  (reflectionGL reflectionQ det_reflectionQ_real vhValueFull)
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
  (binaryRationalReal binaryRationalFinite)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation (ιGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegConj
  (vhValueNeg_eq_conj conj_ιGL reflectionQ_mul_self_GL qv_reflection evM_map_rat)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegPoint
  (exists_block blockGL blockGL_val reflect_blockGL)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegK0 (K0Spec_neg)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibreG
  (shellIntegrandG shellIntegrandG_eq_block)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic (IntGL OS)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof (evM)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegG

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The reflection `diag(1,-1)` in `GL₂(K)` is its own inverse. -/
theorem reflectionGL_mul_self (K : Type*) [Field K] :
    reflectionGL K * reflectionGL K = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  show (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) K) * !![1, 0; 0, -1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix form of `reflectionGL_mul_self`. -/
theorem reflect_mul_self_mat (K : Type*) [Field K] :
    (reflectionGL K).val * (reflectionGL K).val = 1 := by
  rw [← Units.val_mul, reflectionGL_mul_self, Units.val_one]

/-- The matrix of `diag(1,-1)`. -/
theorem reflectionGL_val (K : Type*) [Field K] :
    (reflectionGL K).val = !![(1 : K), 0; 0, -1] := rfl

/-- Each entry of `diag(1,-1) Y diag(1,-1)` is a sign times the entry of `Y`. -/
theorem reflect_conj_entry (K : Type*) [Field K] (Y : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    ((reflectionGL K).val * Y * (reflectionGL K).val) i j =
      (![(1 : K), -1] i * ![(1 : K), -1] j) * Y i j := by
  rw [reflectionGL_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- The sign `s_i s_j` with `s = (1,-1)` is `1` or `-1`. -/
theorem sign_mul_cases (K : Type*) [Field K] (i j : Fin 2) :
    ![(1 : K), -1] i * ![(1 : K), -1] j = 1 ∨ ![(1 : K), -1] i * ![(1 : K), -1] j = -1 := by
  fin_cases i <;> fin_cases j <;> simp

/-- Conjugation by `diag(1,-1)` preserves `IntGL` at a finite place: the determinant is unchanged,
and every entry of the conjugate is `±` an entry of the original. -/
theorem intGL_reflect (v : FinitePlace) (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hX : IntGL v X) :
    IntGL v ((reflectionGL (v.adicCompletion ℚ)).val * X * (reflectionGL (v.adicCompletion ℚ)).val) := by
  obtain ⟨hdet, hent, hinv⟩ := hX
  have hRR := reflect_mul_self_mat (v.adicCompletion ℚ)
  have hRdet : (reflectionGL (v.adicCompletion ℚ)).val.det = -1 := by
    show (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = -1
    rw [Matrix.det_fin_two_of]
    ring
  have hdetEq : ((reflectionGL (v.adicCompletion ℚ)).val * X * (reflectionGL (v.adicCompletion ℚ)).val).det
      = X.det := by
    rw [Matrix.det_mul, Matrix.det_mul, hRdet]
    ring
  have hRep : ∀ Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, Y i j ∈ OS v) →
      ∀ i j, ((reflectionGL (v.adicCompletion ℚ)).val * Y * (reflectionGL (v.adicCompletion ℚ)).val) i j
        ∈ OS v := by
    intro Y hY i j
    rw [reflect_conj_entry]
    rcases sign_mul_cases (v.adicCompletion ℚ) i j with h1 | h1 <;> rw [h1]
    · rw [one_mul]
      exact hY i j
    · rw [neg_one_mul]
      exact neg_mem (hY i j)
  refine ⟨?_, hRep X hent, ?_⟩
  · rw [hdetEq]
    exact hdet
  · have hinvEq : ((reflectionGL (v.adicCompletion ℚ)).val * X * (reflectionGL (v.adicCompletion ℚ)).val)⁻¹ =
        (reflectionGL (v.adicCompletion ℚ)).val * X⁻¹ * (reflectionGL (v.adicCompletion ℚ)).val := by
      apply Matrix.inv_eq_right_inv
      have hXX : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hdet
      calc (reflectionGL (v.adicCompletion ℚ)).val * X * (reflectionGL (v.adicCompletion ℚ)).val *
            ((reflectionGL (v.adicCompletion ℚ)).val * X⁻¹ * (reflectionGL (v.adicCompletion ℚ)).val)
          = (reflectionGL (v.adicCompletion ℚ)).val *
              (X * ((reflectionGL (v.adicCompletion ℚ)).val * (reflectionGL (v.adicCompletion ℚ)).val) * X⁻¹) *
              (reflectionGL (v.adicCompletion ℚ)).val := by
            simp only [Matrix.mul_assoc]
        _ = (reflectionGL (v.adicCompletion ℚ)).val * (X * X⁻¹) * (reflectionGL (v.adicCompletion ℚ)).val := by
            rw [hRR, Matrix.mul_one]
        _ = (reflectionGL (v.adicCompletion ℚ)).val * (reflectionGL (v.adicCompletion ℚ)).val := by
            rw [hXX, Matrix.mul_one]
        _ = 1 := hRR
    intro i j
    rw [hinvEq]
    exact hRep _ hinv i j

/-- Conjugation by the rational reflection `R` in `GL₂(𝔸_f)` is an involution in the group. -/
theorem reflectionF_mul_self :
    binaryRationalFinite reflectionQ * binaryRationalFinite reflectionQ = 1 := by
  rw [← map_mul, reflectionQ_mul_self_GL, map_one]

/-- The conjugation identity in `GL₂(𝔸_f)`: `(R a R)(R b R)(R c R) = R (a b c) R`. -/
theorem conj_assoc (Rf a b c : BinaryFiniteGL) (hRR : Rf * Rf = 1) :
    (Rf * a * Rf) * ((Rf * b * Rf) * (Rf * c * Rf)) = Rf * (a * (b * c)) * Rf := by
  have hc : ∀ x : BinaryFiniteGL, Rf * (Rf * x) = x := fun x => by
    rw [← mul_assoc, hRR, one_mul]
  simp only [mul_assoc, hc]

/-- The determinant of the reflected base point is unchanged. -/
theorem det_reflect_base (gf : BinaryFiniteGL) :
    Matrix.GeneralLinearGroup.det (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ) =
      Matrix.GeneralLinearGroup.det gf := by
  have hRR : Matrix.GeneralLinearGroup.det (binaryRationalFinite reflectionQ) *
      Matrix.GeneralLinearGroup.det (binaryRationalFinite reflectionQ) = 1 := by
    rw [← map_mul, ← map_mul, reflectionQ_mul_self_GL]
    simp only [map_one]
  simp only [map_mul]
  rw [mul_right_comm, hRR, one_mul]

/-- **The sign identity at a general base point.** For `det g∞ < 0` and `z ∈ ℚ_p²`, the literal
integrand at `(g_f, g∞)` equals the literal integrand at `(R g_f R, R g∞)` evaluated at `(z.1, -z.2)`.
-/
theorem shellIntegrandG_neg (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hgInf : (Matrix.GeneralLinearGroup.det gInf).val < 0)
    (gf : BinaryFiniteGL) (gp : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hgp : gf.val.map (finiteEvaluation v) = gp.val) (hgI : IntGL v gp.val)
    (z : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
    shellIntegrandG v I gf gInf z =
      shellIntegrandG v I (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ)
        (binaryRationalReal reflectionQ * gInf) (z.1, -z.2) := by
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
  have hRf : (binaryRationalFinite reflectionQ).val.map (finiteEvaluation v) =
      (reflectionGL (v.adicCompletion ℚ)).val := by
    show evM v (reflectionQ.val.map (algebraMap ℚ FiniteAdeles)) = _
    rw [evM_map_rat, qv_reflection]
  have hgp' : (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ).val.map
      (finiteEvaluation v) =
      (reflectionGL (v.adicCompletion ℚ) * gp * reflectionGL (v.adicCompletion ℚ)).val := by
    simp only [Units.val_mul, Matrix.map_mul, hRf, hgp]
  have hgI' : IntGL v (reflectionGL (v.adicCompletion ℚ) * gp * reflectionGL (v.adicCompletion ℚ)).val := by
    rw [Units.val_mul, Units.val_mul]
    exact intGL_reflect v gp.val hgI
  have hinvconj : (reflectionGL (v.adicCompletion ℚ) * gp * reflectionGL (v.adicCompletion ℚ))⁻¹ =
      reflectionGL (v.adicCompletion ℚ) * gp⁻¹ * reflectionGL (v.adicCompletion ℚ) := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_right (reflectionGL_mul_self (v.adicCompletion ℚ)),
      mul_assoc]
  have L := shellIntegrandG_eq_block v I h hform gInf (z := z) hK (blockGL v hdet) (blockGL_val v hdet)
    gf gp hgp hgI
  have R := shellIntegrandG_eq_block v I h hform (binaryRationalReal reflectionQ * gInf) (z := (z.1, -z.2))
    hK' (reflectionGL (v.adicCompletion ℚ) * blockGL v hdet * reflectionGL (v.adicCompletion ℚ))
    (fun i j => by rw [reflect_blockGL v hdet]; rfl)
    (binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ)
    (reflectionGL (v.adicCompletion ℚ) * gp * reflectionGL (v.adicCompletion ℚ)) hgp' hgI'
  have hvh : vhValueFull (-2 * I.halfWeight) h gInf (ιGL v (blockGL v hdet) * (gf * ιGL v gp⁻¹)) =
      vhValueFull (-2 * I.halfWeight) h (binaryRationalReal reflectionQ * gInf)
        (ιGL v (reflectionGL (v.adicCompletion ℚ) * blockGL v hdet * reflectionGL (v.adicCompletion ℚ)) *
          ((binaryRationalFinite reflectionQ * gf * binaryRationalFinite reflectionQ) *
            ιGL v ((reflectionGL (v.adicCompletion ℚ) * gp * reflectionGL (v.adicCompletion ℚ))⁻¹))) := by
    unfold vhValueFull
    rw [ite_eq_right (not_lt.2 hgInf.le), ite_eq_left hRg,
      vhValueNeg_eq_conj _ h gInf hgInf (ιGL v (blockGL v hdet) * (gf * ιGL v gp⁻¹)),
      hinvconj, ← conj_ιGL v gp⁻¹, ← conj_ιGL v (blockGL v hdet),
      conj_assoc (binaryRationalFinite reflectionQ) _ _ _ reflectionF_mul_self]
  rw [L, R, det_reflect_base gf, hvh]

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitNegG

end
