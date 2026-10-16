module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.CyclicAdelic
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Substitution
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Haar
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.FibreFinite
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.HermiteCount
public import TernaryPeriodPolynomials.PeriodPolynomial.Defs

@[expose] public section


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
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary (Fh lowMat Gl Gl_eq lowMat_det_ne_zero)
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeTransform
  (latSum vhRight latSum_diag latSum_mul_integral_of_perm vhRight_mul_integral vhRight_diag)
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeRecursion (eq_cyclic_hecke_finite_one)
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (HasPrimeHeckeRelations)
open TernaryPeriodPolynomials.Argument.LatticeCounts (hnfData mem_hnfData cyclicHNF)
/-!
# The shell-sum bundle and the matching with the `unramified_local_factor`

Formalized by Claude Haiku 5.5.

The shell of
valuation `s ≥ 1` contributes `(1-p⁻¹) p^{-s(k-2)} {a_h(p^s) - p^{k-2} a_h(p^{s-2})} v_h`, and the
integral over `ℤ_p²` contributes `v_h`.

Ingredients, all proved elsewhere:
* `shellHaarMeasure v s`: the ShellHaar measure of the shell (`shell_measure_finitePlace`), value
  `p^{2s} - p^{2s-2}` (`shellHaarMeasure_eq`);
* the cyclic count `card cyclicHNF p s = p^s + p^{s-1}` (`card_cyclicHNF`);
* the finite factor `|det A|_p^{k/2} = p^{-s k/2}` (`ShellSubstitution.finite_factor`, the real
  exponent form is used in the hypothesis and `finite_factor` is cited in `shell_real_identity`'s
  docstring);
* the cyclic Hecke sum `H1_cyc` (eq:cyclic-hecke at finite coordinate one, proved in
  `LatticeCyclicAdelic`).

THE ONE EXPLICIT HYPOTHESIS `hSeed` (the p-adic seed-transform law for the shell): the shell value `shellVal s` is the finite factor times the cyclic Hecke sum of
`v_h`, weighted per cyclic lattice by its share `shellHaarMeasure v s / #cyclicHNF p s` of the
shell measure. The equal share per cyclic lattice is NOT derived: it needs `GL₂(ℤ_p)`-transitivity
on cyclic lattices of index `p^s`, which is not in the library. It is an input of `hSeed`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.ShellBundle

open MeasureTheory Matrix
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeCyclicAdelic (H1_cyc)
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue (vhValue)
open TernaryPeriodPolynomials.Argument.LatticeCounts (cyclicHNF hnfData card_cyclicHNF)
open TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
  (pairShell pairLat hermLat shell_measure_finitePlace hermLat_fibre_measure_finitePlace)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (finitePadicMeasure HasPrimeHeckeRelations)
open TernaryPeriodPolynomials.Argument (fourierCoeff IsNormalizedEigenform)

/-- The real value of the ShellHaar measure of the shell of valuation `s` at the finite place `v`:
the product of the local Haar measure `finitePadicMeasure v` with itself, on `pairShell p s`. -/
def shellHaarMeasure (v : FinitePlace) (s : ℕ) : ℝ :=
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  ((finitePadicMeasure v).prod (finitePadicMeasure v)
    (pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s)).toReal

/-- The shell measure is `p^{2s} - p^{2s-2}` (ShellHaar, `s ≥ 1`). -/
theorem shellHaarMeasure_eq (v : FinitePlace) {s : ℕ} (hs : 1 ≤ s) :
    shellHaarMeasure v s =
      (((Rat.HeightOneSpectrum.primesEquiv v).val ^ (2 * s) -
        (Rat.HeightOneSpectrum.primesEquiv v).val ^ (2 * s - 2) : ℕ) : ℝ) := by
  unfold shellHaarMeasure
  rw [shell_measure_finitePlace v hs, ENNReal.toReal_natCast]

/-- The fibre weight of a Hermite triple `t` in the shell of valuation `s` at the finite place `v`:
the ShellHaar measure of the shell points whose lattice is `L_t = hermLat p t`. -/
def fibreWeight (v : FinitePlace) (s : ℕ) (t : ℕ × ℕ × ℕ) : ℝ :=
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  ((finitePadicMeasure v).prod (finitePadicMeasure v)
    {z | z ∈ pairShell (Rat.HeightOneSpectrum.primesEquiv v).val s ∧
      (pairLat (Rat.HeightOneSpectrum.primesEquiv v).val z).toAddSubgroup =
        (hermLat (Rat.HeightOneSpectrum.primesEquiv v).val t).toAddSubgroup}).toReal

/-- For a cyclic triple `t` of level `p^s` (`s ≥ 1`), the fibre weight is `p^s - p^{s-1}`
(`hermLat_fibre_measure_finitePlace`). -/
theorem fibreWeight_eq (v : FinitePlace) {s : ℕ} (hs : 1 ≤ s) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ cyclicHNF (Rat.HeightOneSpectrum.primesEquiv v).val s) :
    fibreWeight v s t = (((Rat.HeightOneSpectrum.primesEquiv v).val ^ s -
      (Rat.HeightOneSpectrum.primesEquiv v).val ^ (s - 1) : ℕ) : ℝ) := by
  unfold fibreWeight
  rw [hermLat_fibre_measure_finitePlace v hs ht, ENNReal.toReal_natCast]

/-- **The equal share, derived.** For a cyclic triple `t` of level `p^s` (`s ≥ 1`), the fibre
weight is the shell measure divided by the number of cyclic triples: `p^{2s} - p^{2s-2}` over
`p^s + p^{s-1}` is `p^s - p^{s-1}`. -/
theorem fibreWeight_eq_share (v : FinitePlace) (p : Nat.Primes)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val) {s : ℕ} (hs : 1 ≤ s)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ cyclicHNF p.val s) :
    fibreWeight v s t = shellHaarMeasure v s / ((cyclicHNF p.val s).card : ℝ) := by
  have ht' : t ∈ cyclicHNF (Rat.HeightOneSpectrum.primesEquiv v).val s := by
    rw [hv]
    exact ht
  have : Fact p.val.Prime := ⟨p.property⟩
  rw [fibreWeight_eq v hs ht', shellHaarMeasure_eq v hs, hv, card_cyclicHNF hs]
  have hpos : 0 < p.val ^ s := pow_pos p.property.pos s
  have hden : ((p.val ^ s + p.val ^ (s - 1) : ℕ) : ℝ) ≠ 0 := by
    have : 0 < p.val ^ s + p.val ^ (s - 1) := Nat.lt_of_lt_of_le hpos (Nat.le_add_right _ _)
    exact_mod_cast this.ne'
  have hle1 : p.val ^ (s - 1) ≤ p.val ^ s := Nat.pow_le_pow_right p.property.pos (by omega)
  have hle2 : p.val ^ (2 * s - 2) ≤ p.val ^ (2 * s) :=
    Nat.pow_le_pow_right p.property.pos (by omega)
  rw [eq_div_iff hden, Nat.cast_sub hle1, Nat.cast_sub hle2]
  push_cast
  rw [show 2 * s - 2 = (s - 1) + (s - 1) by omega, show 2 * s = s + s by ring]
  simp only [pow_add]
  ring

/-- Real identity behind the shell: the shell weight `(x^{2s}-x^{2s-2})/(x^s+x^{s-1})` times the
finite factor `x^{-s k/2}` times `(x^s)^{1-k/2}` is `(1-x⁻¹) x^{-s(k-2)}`, for `s ≥ 1`.
The finite factor is `ShellSubstitution.finite_factor` with `det A = p^s`. -/
theorem shell_real_identity (x : ℝ) (hx : 1 < x) (k : ℤ) (s : ℕ) (hs : 1 ≤ s) :
    (((x ^ (2 * s) - x ^ (2 * s - 2)) / (x ^ s + x ^ (s - 1))) *
      x ^ (-(s : ℝ) * ((k : ℝ) / 2))) * (x ^ s) ^ (1 - (k : ℝ) / 2) =
      (1 - x⁻¹) * x ^ (-(s : ℝ) * ((k : ℝ) - 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  have hx0 : 0 < x := zero_lt_one.trans hx
  have e2 : 2 * (m + 1) - 2 = 2 * m := by omega
  have e1 : m + 1 - 1 = m := by omega
  rw [e2, e1]
  have key : (x ^ (2 * (m + 1)) - x ^ (2 * m)) / (x ^ (m + 1) + x ^ m) =
      x ^ (m + 1) * (1 - x⁻¹) := by
    have hpos : x ^ (m + 1) + x ^ m ≠ 0 := by positivity
    rw [div_eq_iff hpos]
    field_simp
    ring
  rw [key, ← Real.rpow_natCast x (m + 1), ← Real.rpow_mul hx0.le]
  have hexp : ((m + 1 : ℕ) : ℝ) + (-((m + 1 : ℕ) : ℝ) * ((k : ℝ) / 2)) +
      ((m + 1 : ℕ) : ℝ) * (1 - (k : ℝ) / 2) = -((m + 1 : ℕ) : ℝ) * ((k : ℝ) - 2) := by
    push_cast; ring
  have hsplit : x ^ (((m + 1 : ℕ) : ℝ) + (-((m + 1 : ℕ) : ℝ) * ((k : ℝ) / 2)) +
      ((m + 1 : ℕ) : ℝ) * (1 - (k : ℝ) / 2)) =
      x ^ ((m + 1 : ℕ) : ℝ) * x ^ (-((m + 1 : ℕ) : ℝ) * ((k : ℝ) / 2)) *
        x ^ (((m + 1 : ℕ) : ℝ) * (1 - (k : ℝ) / 2)) := by
    rw [Real.rpow_add hx0, Real.rpow_add hx0]
  rw [hexp] at hsplit
  rw [hsplit]
  ring

/-- Complex power of a real power: `((x^s : ℝ) : ℂ)^{1-k/2} = ((x^s)^{1-k/2} : ℝ)` for `x ≥ 0`. -/
theorem cpow_shell_eq_real (x : ℝ) (hx : 0 ≤ x) (s : ℕ) (k : ℤ) :
    (((x ^ s : ℝ)) : ℂ) ^ (1 - (k : ℂ) / 2) = ((((x ^ s) ^ (1 - (k : ℝ) / 2)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (pow_nonneg hx s)]
  congr 1
  push_cast
  ring

/-- Complex integer power of a real power: `(x : ℂ)^{-(s(k-2))} = (x^{-s(k-2)} : ℝ)`. -/
theorem zpow_shell_eq_real (x : ℝ) (s : ℕ) (k : ℤ) :
    (x : ℂ) ^ (-((s : ℤ) * (k - 2))) = ((x ^ (-(s : ℝ) * ((k : ℝ) - 2)) : ℝ) : ℂ) := by
  have e : -(s : ℝ) * ((k : ℝ) - 2) = (((-((s : ℤ) * (k - 2))) : ℤ) : ℝ) := by push_cast; ring
  rw [e, Real.rpow_intCast, Complex.ofReal_zpow]

/-- **The shell-sum bundle, as ONE theorem with ONE explicit hypothesis.**

The hypothesis `hSeed` is the seed-transform law of the shell of valuation `s ≥ 1` only: the shell
value `shellVal s` equals the finite factor `p^{-s k/2}` (`ShellSubstitution.finite_factor`) times
the sum over cyclic Hermite triples `t` of the fibre weight `fibreWeight v s t` (the ShellHaar
measure of the shell points whose lattice is `L_t`) times `v_h` at the cyclic lift of `t`. The equal share per cyclic lattice is NOT assumed: it is derived in the proof from
the fibre count `fibreWeight_eq_share`.

Conclusions:
1. the per-shell contribution `(1-p⁻¹) p^{-s(k-2)} {a_h(p^s) - p^{k-2} a_h(p^{s-2})} v_h`
   (`a_h(p^{-1}) = 0`, expressed by the `if 2 ≤ s` guard);
2. the sum over `r ≥ 0` of the shells `s = r+1`, plus the `ℤ_p²` term `v_h`, equals `v_h` times the
   left side of `unramified_local_factor` (`1 + (1-p⁻¹) ∑_r p^{-(r+1)(k-2)} ...`). -/
theorem shell_sum_bundle (k : ℤ) (h : CuspForm levelOne k) (hh : IsNormalizedEigenform h)
    (p : Nat.Primes) (v : FinitePlace)
    (hv : ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p.val)
    (B : ℕ × ℕ × ℕ → GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (hB : ∀ s : ℕ, ∀ t ∈ hnfData (p.val ^ s),
      (B t).val = (intMat t).map (Int.cast : ℤ → v.adicCompletion ℚ))
    (gInf : BinaryRealGL) (hgInf : 0 < (Matrix.GeneralLinearGroup.det gInf).val)
    (shellVal : ℕ → ℂ)
    (hSeed : ∀ s : ℕ, 1 ≤ s →
      shellVal s = (((p.val : ℝ) ^ (-(s : ℝ) * ((k : ℝ) / 2)) : ℝ) : ℂ) *
        ∑ t ∈ cyclicHNF p.val s, ((fibreWeight v s t : ℝ) : ℂ) * vhValue k h gInf (ιGL v (B t))) :
    (∀ s : ℕ, 1 ≤ s → shellVal s = vhValue k h gInf 1 *
        ((1 - ((p.val : ℕ) : ℂ)⁻¹) * ((p.val : ℕ) : ℂ) ^ (-((s : ℤ) * (k - 2))) *
          (fourierCoeff h (p.val ^ s) -
            ((p.val : ℕ) : ℂ) ^ (k - 2) * (if 2 ≤ s then fourierCoeff h (p.val ^ (s - 2)) else 0)))) ∧
    vhValue k h gInf 1 + ∑' r : ℕ, shellVal (r + 1) =
      vhValue k h gInf 1 * (1 + (1 - ((p.val : ℕ) : ℂ)⁻¹) * ∑' r : ℕ,
        ((p.val : ℕ) : ℂ) ^ (-(((r : ℤ) + 1) * (k - 2))) *
          (fourierCoeff h (p.val ^ (r + 1)) -
            ((p.val : ℕ) : ℂ) ^ (k - 2) * (if r = 0 then 0 else fourierCoeff h (p.val ^ (r - 1))))) := by
  obtain ⟨hnorm, eig, rel⟩ := hh
  have : Fact p.val.Prime := ⟨p.property⟩
  have hx : (1 : ℝ) < (p.val : ℝ) := by exact_mod_cast p.property.one_lt
  have hx0 : (0 : ℝ) < (p.val : ℝ) := by linarith
  have hfc : ∀ m : ℕ, fourierCoeff h m = (UpperHalfPlane.qExpansion 1 h).coeff m := by
    intro m
    unfold fourierCoeff
    simp only [Subgroup.strictWidthInfty_SL2Z]
  -- The equal share, derived from the fibre count (`fibreWeight_eq_share`).
  have hsumS : ∀ s : ℕ, 1 ≤ s →
      ∑ t ∈ cyclicHNF p.val s, ((fibreWeight v s t : ℝ) : ℂ) * vhValue k h gInf (ιGL v (B t)) =
        ((shellHaarMeasure v s / ((cyclicHNF p.val s).card : ℝ) : ℝ) : ℂ) *
          ∑ t ∈ cyclicHNF p.val s, vhValue k h gInf (ιGL v (B t)) := by
    intro s hs
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t ht => by rw [fibreWeight_eq_share v p hv hs ht]
  have hpS : ∀ s : ℕ, 1 ≤ s → shellVal s = vhValue k h gInf 1 *
      ((1 - ((p.val : ℕ) : ℂ)⁻¹) * ((p.val : ℕ) : ℂ) ^ (-((s : ℤ) * (k - 2))) *
        (fourierCoeff h (p.val ^ s) -
          ((p.val : ℕ) : ℂ) ^ (k - 2) * (if 2 ≤ s then fourierCoeff h (p.val ^ (s - 2)) else 0))) := by
    intro s hs
    have hH := H1_cyc k h eig rel (by rw [← hfc]; exact hnorm) p s v hv B (hB s) gInf hgInf
    simp only [← hfc] at hH
    rw [hSeed s hs, hsumS s hs, hH, shellHaarMeasure_eq v hs, hv, card_cyclicHNF hs]
    have hM : ((p.val ^ (2 * s) - p.val ^ (2 * s - 2) : ℕ) : ℝ) =
        (p.val : ℝ) ^ (2 * s) - (p.val : ℝ) ^ (2 * s - 2) := by
      rw [Nat.cast_sub (Nat.pow_le_pow_right p.property.pos (by omega))]
      push_cast
      ring
    have main : (((p.val ^ (2 * s) - p.val ^ (2 * s - 2) : ℕ) : ℝ) /
        ((p.val ^ s + p.val ^ (s - 1) : ℕ) : ℝ)) *
        (p.val : ℝ) ^ (-(s : ℝ) * ((k : ℝ) / 2)) * ((p.val : ℝ) ^ s) ^ (1 - (k : ℝ) / 2) =
        (1 - (p.val : ℝ)⁻¹) * (p.val : ℝ) ^ (-(s : ℝ) * ((k : ℝ) - 2)) := by
      rw [hM]
      have hC : ((p.val ^ s + p.val ^ (s - 1) : ℕ) : ℝ) = (p.val : ℝ) ^ s + (p.val : ℝ) ^ (s - 1) := by
        push_cast
        ring
      rw [hC]
      exact shell_real_identity (p.val : ℝ) hx k s hs
    have hR : ((p.val ^ s : ℕ) : ℂ) ^ (1 - (k : ℂ) / 2) =
        ((((p.val : ℝ) ^ s) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) := by
      rw [show ((p.val ^ s : ℕ) : ℂ) = (((p.val : ℝ) ^ s : ℝ) : ℂ) by push_cast; ring]
      exact cpow_shell_eq_real (p.val : ℝ) hx0.le s k
    have hz : ((p.val : ℕ) : ℂ) ^ (-((s : ℤ) * (k - 2))) =
        ((((p.val : ℝ)) ^ (-(s : ℝ) * ((k : ℝ) - 2)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, zpow_shell_eq_real]
    have hone : (1 - ((p.val : ℕ) : ℂ)⁻¹) = (((1 - (p.val : ℝ)⁻¹) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hR, hz, hone]
    have hk := congrArg (fun r : ℝ => (r : ℂ)) main
    simp only [Complex.ofReal_mul] at hk
    set Zc := fourierCoeff h (p.val ^ s) -
      ((p.val : ℕ) : ℂ) ^ (k - 2) * (if 2 ≤ s then fourierCoeff h (p.val ^ (s - 2)) else 0) with hZc
    set V := vhValue k h gInf 1 with hV
    linear_combination (Zc * V) * hk
  refine ⟨hpS, ?_⟩
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
  have hsum : ∑' r : ℕ, shellVal (r + 1) =
      vhValue k h gInf 1 * ((1 - ((p.val : ℕ) : ℂ)⁻¹) * ∑' r : ℕ,
        ((p.val : ℕ) : ℂ) ^ (-(((r : ℤ) + 1) * (k - 2))) *
          (fourierCoeff h (p.val ^ (r + 1)) -
            ((p.val : ℕ) : ℂ) ^ (k - 2) * (if r = 0 then 0 else fourierCoeff h (p.val ^ (r - 1))))) := by
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_mul_left]
  rw [hsum]
  ring

end TernaryPeriodPolynomials.Argument.LatticeCounts.ShellBundle

end
