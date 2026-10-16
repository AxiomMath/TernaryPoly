module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KSeedBound
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KLineValues

@[expose] public section


/-!
# The printed form of the line-row orbit integrals

Paper: Appendix C.5 and `eq:intertwiner`.

Combining `lineA1K_eval` (Bruhat evaluation) with the bridge `Tinf_eq_lineSeed` and the explicit values of
`LineKLineValues`: for every face point `x` and every coefficient `(p, q, m)`

`lineA1K b x p q m = N⁻² Σ_o cx b (cx (sign o) (c_∞ · h_o(τ_x) · W(p,q) · coeff_m (τ_x Z - Y)ⁿ))`

(`lineA1K_printed`), with `τ_x = -x₂ + i x₃`, `c_∞ = -2πi/(n+1)`, `W` the wedge table. The coefficients with
`m₀ ≠ 0` vanish (`lineA1K_eq_zero_of_ne`); the `(0, 2)` entry of the `Yⁿ` coefficient is the series of orbit
seeds at `τ_x` (`lineA1K_Yn`).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial ComplexConjugate
open scoped MatrixGroups Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.FormClassK
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization (lineChart lineTau)

section Tinf

variable (n : ℕ)

/-- The constant `c_∞ = -2πi/(n+1)` of the intertwining integral. -/
def cinf : ℂ := -2 * Real.pi * Complex.I / ((n : ℂ) + 1)

/-- **`m₀ ≥ 1` vanishing**: the real intertwining integral of any admissible seed has zero coefficient at every
`m` with `m 0 ≠ 0`, at every face point and for every pair. -/
theorem Tinf_eq_zero_of_ne (hn : 3 ≤ n) (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im}) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) (hm : m 0 ≠ 0) : Tinf n h x p q m = 0 := by
  rw [Tinf_eq_lineSeed n hn h hh M hM hx p q m, coeff_lineLin_pow_of_ne _ n m hm]
  simp

/-- **The `Yⁿ`-coefficient at the pair `(0, 2)`**: `c_∞ (-1)ⁿ h(τ_x)` with `τ_x = -x₂ + i x₃`. -/
theorem Tinf_Yn_pair02 (hn : 3 ≤ n) (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im}) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) {x : Face} (hx : x ∈ faceSet) :
    Tinf n h x 0 2 (Finsupp.single 1 n) =
      cinf n * ((-1) ^ n * h ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ))) := by
  rw [Tinf_eq_lineSeed n hn h hh M hM hx 0 2 _, lineWedge_02 hx, lineTau_gx hx, coeff_lineLin_pow_Yn]
  unfold cinf
  ring

end Tinf


section Orbit

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- The index set of the free orbits of the line row (`r₀ ≠ 0`). -/
abbrev OrbIdx : Type := {o : Quotient (qActK N k).orbSetoid // (qActK N k).r0Q o ≠ 0}

theorem orbitMat_ne (o : OrbIdx N k) : orbitMat N k (Quotient.out o.1) 2 0 ≠ 0 := by
  have hr : cuspRow (gammaN N) (CuspData.ofSL k).r (Quotient.out o.1) 0 ≠ 0 := by
    have := o.2
    rw [QAct.r0Q_out] at this
    exact this
  rw [orbitMat_row0]
  exact_mod_cast hr

/-- **The printed form of the orbit integrals**: for every face point and every coefficient. -/
theorem lineA1K_printed (hn : 3 ≤ n) (b : Bool) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) :
    lineA1K N k n f b x p q m = ((N : ℂ) ^ 2)⁻¹ * ∑' o : OrbIdx N k,
      cx b (cx (orbitSign N k (Quotient.out o.1))
        (cinf n * (orbitSeed N k n f (Quotient.out o.1) ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) *
          lineWedge x p q * ((C ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) * X 2 - X 1 :
            MvPolynomial (Fin 3) ℂ) ^ n).coeff m))) := by
  rw [lineA1K_eval N k n f b hx]
  congr 1
  refine tsum_congr fun o => ?_
  obtain ⟨hd, M, hM⟩ := orbitSeed_data N k n f _ (orbitMat_ne N k o)
  rw [Tinf_eq_lineSeed n hn _ hd M hM hx p q m, lineTau_gx hx]
  unfold cinf
  ring_nf

/-- **`lineA1K` vanishes for `m₀ ≠ 0`** (at every face point and every pair). -/
theorem lineA1K_eq_zero_of_ne (hn : 3 ≤ n) (b : Bool) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) (hm : m 0 ≠ 0) : lineA1K N k n f b x p q m = 0 := by
  rw [lineA1K_printed N k n f hn b hx, coeff_lineLin_pow_of_ne _ n m hm]
  simp

/-- **The `Yⁿ` coefficient at the pair `(0, 2)`** as the series of orbit seeds at `τ_x`. -/
theorem lineA1K_Yn (hn : 3 ≤ n) (b : Bool) {x : Face} (hx : x ∈ faceSet) :
    lineA1K N k n f b x 0 2 (Finsupp.single 1 n) = ((N : ℂ) ^ 2)⁻¹ * ∑' o : OrbIdx N k,
      cx b (cx (orbitSign N k (Quotient.out o.1))
        (cinf n * ((-1) ^ n * orbitSeed N k n f (Quotient.out o.1) ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ))))) := by
  rw [lineA1K_eval N k n f b hx]
  congr 1
  refine tsum_congr fun o => ?_
  obtain ⟨hd, M, hM⟩ := orbitSeed_data N k n f _ (orbitMat_ne N k o)
  rw [Tinf_Yn_pair02 n hn _ hd M hM hx]

end Orbit

end TernaryPeriodPolynomials.Argument.EisensteinClass
