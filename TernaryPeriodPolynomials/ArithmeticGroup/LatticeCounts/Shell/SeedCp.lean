module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Bundle
public import TernaryPeriodPolynomials.ArithmeticGroup.UnramifiedFactor

@[expose] public section


/-!
# The shell sum equals `v_h · c_p`, conditional only on `hSeed`

Formalized by Claude Haiku 5.5.

Matches `ShellBundle.shell_sum_bundle` with the target
`TernaryPeriodPolynomials.unramified_local_factor` (Appendix C.6, the unramified
factor `c_p = L_p(h, k-2)/L_p(h, k-1)`). The only hypothesis beyond the statement's
setting is the seed-transform law `hSeed` of the shell (`ShellBundle`), in which the equal share
per cyclic lattice is derived from the fibre count (`fibreWeight_eq_share`).

Conclusion 1 is the summability of the shell terms `shellVal (r+1)`, transported from the summability clause by `Summable.mul_left`. Conclusion 2 is
`v_h + ∑_{r≥0} shellVal (r+1) = v_h · c_p`.
-/

open Matrix PadicInt
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalIwasawa (PInt)
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeBasisChange
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermZp
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeCyclicZp
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof
open TernaryPeriodPolynomials.Argument.LatticeCounts.IotaValue
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue (vhValue)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.Argument.LatticeCounts (hnfData mem_hnfData cyclicHNF)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellBundle

open MeasureTheory Matrix
open TernaryPeriodPolynomials.Argument (fourierCoeff IsNormalizedEigenform)

/-- **The shell sum matches the unramified factor.** Under the seed-transform law `hSeed`
alone, the shells `s = r + 1` are summable and sum, with `v_h`, to `v_h · c_p`, where `c_p` is the
right-hand side of the `unramified_local_factor`. -/
theorem shell_total_eq_cp {k : ℤ} (hk : 6 < k) (h : CuspForm levelOne k)
    (hh : IsNormalizedEigenform h) (p : Nat.Primes) (v : FinitePlace)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (B : ℕ × ℕ × ℕ → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : ∀ s : ℕ, ∀ t ∈ hnfData (p.val ^ s),
      (B t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ))
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (shellVal : ℕ → ℂ)
    (hSeed : ∀ s : ℕ, 1 ≤ s →
      shellVal s = (((p.val : ℝ) ^ (-(s : ℝ) * ((k : ℝ) / 2)) : ℝ) : ℂ) *
        ∑ t ∈ cyclicHNF p.val s, ((fibreWeight v s t : ℝ) : ℂ) * vhValue k h gInf (ιGL v (B t))) :
    Summable (fun r : ℕ => shellVal (r + 1)) ∧
    vhValue k h gInf 1 + ∑' r : ℕ, shellVal (r + 1) =
      vhValue k h gInf 1 * ((1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (1 - k) +
        ((p : ℕ) : ℂ) ^ (1 - k)) /
        (1 - fourierCoeff h (p : ℕ) * ((p : ℕ) : ℂ) ^ (2 - k) + ((p : ℕ) : ℂ) ^ (3 - k))) := by
  obtain ⟨hpS, hcons2⟩ := shell_sum_bundle k h hh p v hv B hB gInf hgInf shellVal hSeed
  obtain ⟨hsum, hcp⟩ := TernaryPeriodPolynomials.unramified_local_factor hk h hh p
  have hterm : ∀ r : ℕ, shellVal (r + 1) = vhValue k h gInf 1 * ((1 - ((p.val : ℕ) : ℂ)⁻¹) *
      (((p.val : ℕ) : ℂ) ^ (-(((r : ℤ) + 1) * (k - 2))) *
        (fourierCoeff h (p.val ^ (r + 1)) -
          ((p.val : ℕ) : ℂ) ^ (k - 2) * (if r = 0 then 0 else fourierCoeff h (p.val ^ (r - 1)))))) := by
    intro r
    rw [hpS (r + 1) (by omega)]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [ite_eq_right (show ¬ (2 ≤ 0 + 1) by norm_num), ite_eq_left rfl]
      simp only [Nat.cast_zero, Nat.cast_one, zero_add, mul_zero, sub_zero, mul_assoc]
    · rw [ite_eq_left (show 2 ≤ r + 1 by omega), ite_eq_right (show r ≠ 0 by omega),
        show r + 1 - 2 = r - 1 by omega]
      push_cast
      ring
  have hsum' : Summable (fun r : ℕ => shellVal (r + 1)) := by
    refine (hsum.mul_left (vhValue k h gInf 1 * (1 - ((p.val : ℕ) : ℂ)⁻¹))).congr fun r => ?_
    rw [hterm r]
    ring
  refine ⟨hsum', ?_⟩
  rw [hcons2, hcp]

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellBundle

end
