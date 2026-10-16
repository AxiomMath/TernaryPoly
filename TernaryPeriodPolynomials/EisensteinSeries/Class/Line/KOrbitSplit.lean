module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KOrbitSeries

@[expose] public section


/-!
# The two orbit-seed series and the `Yⁿ` coefficient

Paper: Appendix C.5.

The named series `seriesPos τ = Σ_{r₀>0} (h|A_o)(τ)` and `seriesNeg τ = Σ_{r₀<0} hStar(h|A_o⁺)(τ)`, both
absolutely convergent for `Im τ > 0`, and `lineA1K_Yn_series`: at every face point the `Yⁿ`-coefficient of the
radical average at the pair `(0, 2)` is `N⁻² cx b ((-1)ⁿ (c_∞ S₊(τ_x) + conj c_∞ · conj S₋(τ_x)))`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial ComplexConjugate
open scoped MatrixGroups Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.FormClassK
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

section Split

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

theorem orbitMat_pos_iff (o : OrbIdx N k) :
    0 < orbitMat N k (Quotient.out o.1) 2 0 ↔ 0 < (qActK N k).r0Q o.1 := by
  rw [orbitMat_row0, QAct.r0Q_out]
  exact_mod_cast Iff.rfl

theorem orbitMat_neg_iff (o : OrbIdx N k) :
    orbitMat N k (Quotient.out o.1) 2 0 < 0 ↔ (qActK N k).r0Q o.1 < 0 := by
  rw [orbitMat_row0, QAct.r0Q_out]
  exact_mod_cast Iff.rfl

/-- **The positive series** `Σ_{r₀>0} (h|A_o)(τ)`. -/
def seriesPos (τ : ℂ) : ℂ :=
  ∑' o : OrbIdx N k, if 0 < (qActK N k).r0Q o.1 then orbitSeed N k n f (Quotient.out o.1) τ else 0

/-- **The negative series** `Σ_{r₀<0} hStar(h|A_o⁺)(τ)` (before the conjugation that the antiholomorphic
terms carry). -/
def seriesNeg (τ : ℂ) : ℂ :=
  ∑' o : OrbIdx N k, if (qActK N k).r0Q o.1 < 0 then orbitSeed N k n f (Quotient.out o.1) τ else 0

theorem summable_seriesPos (hn : 4 ≤ n) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun o : OrbIdx N k => if 0 < (qActK N k).r0Q o.1 then
      orbitSeed N k n f (Quotient.out o.1) τ else 0) :=
  Summable.of_norm_bounded (summable_orbitSeed N k n f hn hτ) fun o => by
    split_ifs <;> simp

theorem summable_seriesNeg (hn : 4 ≤ n) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun o : OrbIdx N k => if (qActK N k).r0Q o.1 < 0 then
      orbitSeed N k n f (Quotient.out o.1) τ else 0) :=
  Summable.of_norm_bounded (summable_orbitSeed N k n f hn hτ) fun o => by
    split_ifs <;> simp

theorem tsum_split (hn : 4 ≤ n) (b : Bool) {τ : ℂ} (hτ : 0 < τ.im) :
    ∑' o : OrbIdx N k, cx b (cx (orbitSign N k (Quotient.out o.1))
        (cinf n * ((-1) ^ n * orbitSeed N k n f (Quotient.out o.1) τ))) =
      cx b ((-1) ^ n * (cinf n * seriesPos N k n f τ + conj (cinf n) * conj (seriesNeg N k n f τ))) := by
  have hA := summable_seriesPos N k n f hn hτ
  have hB := summable_seriesNeg N k n f hn hτ
  have hB' : Summable (fun o : OrbIdx N k => conj (if (qActK N k).r0Q o.1 < 0 then
      orbitSeed N k n f (Quotient.out o.1) τ else 0)) := hB.star
  rw [seriesPos, seriesNeg, Complex.conj_tsum, ← tsum_mul_left (a := cinf n),
    ← tsum_mul_left (a := conj (cinf n)),
    ← (hA.mul_left (cinf n)).tsum_add (hB'.mul_left (conj (cinf n))),
    ← tsum_mul_left (a := ((-1 : ℂ)) ^ n), cx_tsum]
  refine tsum_congr fun o => ?_
  have hc : ∀ z, cx true z = conj z := fun z => by simp [cx]
  rcases lt_or_gt_of_ne o.2 with hneg | hpos
  · have h1 : orbitMat N k (Quotient.out o.1) 2 0 < 0 := (orbitMat_neg_iff N k o).2 hneg
    have hs : orbitSign N k (Quotient.out o.1) = true := by simp [orbitSign, h1]
    have h2 : ¬ 0 < (qActK N k).r0Q o.1 := not_lt.2 hneg.le
    simp only [hs, h2, ite_false, hneg, ite_true, mul_zero, zero_add, hc, map_mul, map_pow, map_neg, map_one]
    ring
  · have h1 : 0 < orbitMat N k (Quotient.out o.1) 2 0 := (orbitMat_pos_iff N k o).2 hpos
    have hs : orbitSign N k (Quotient.out o.1) = false := by simp [orbitSign, not_lt.2 h1.le]
    have h2 : ¬ (qActK N k).r0Q o.1 < 0 := not_lt.2 hpos.le
    simp only [hs, h2, ite_false, hpos, ite_true, map_zero, mul_zero, add_zero, map_mul, map_pow, map_neg,
      map_one]
    have hc0 : ∀ z, cx false z = z := fun z => by simp [cx]
    simp only [hc0]
    ring

/-- **The `Yⁿ` coefficient at `(0, 2)` is the two orbit-seed series**, at every face point `x`:
`lineA1K b x 0 2 (Yⁿ) = N⁻² cx b ((-1)ⁿ (c_∞ S₊(τ_x) + conj c_∞ · conj S₋(τ_x)))`, `τ_x = -x₂ + i x₃`. -/
theorem lineA1K_Yn_series (hn : 4 ≤ n) (b : Bool) {x : Face} (hx : x ∈ faceSet) :
    lineA1K N k n f b x 0 2 (Finsupp.single 1 n) = ((N : ℂ) ^ 2)⁻¹ *
      cx b ((-1) ^ n * (cinf n * seriesPos N k n f ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) +
        conj (cinf n) * conj (seriesNeg N k n f ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ))))) := by
  rw [lineA1K_Yn N k n f (by omega) b hx]
  congr 1
  exact tsum_split N k n f hn b (by simpa using (show (0 : ℝ) < x 3 from hx))

end Split

end TernaryPeriodPolynomials.Argument.EisensteinClass
