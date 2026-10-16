module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBridgeC

@[expose] public section


/-!
# The antiholomorphic real intertwining integral at a face point has the conjugate scalar `+2πi/(n+1)`

The antiholomorphic seed is the complex conjugate of the holomorphic one, so the real intertwining integral of
the antiholomorphic seed at a face point is the complex conjugate of `Tinf` (`integral_conj`). `Tinf_conj_eq_lineSeed` is the
conjugate of `Tinf_eq_lineSeed`: it is `c̄_∞ = +2πi/(n+1)` times the conjugate line seed
`conj(h(τ_x)) · conj(lineWedge) · coeff_m (τ̄_x Z - Y)ⁿ`.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial ComplexConjugate
open scoped MatrixGroups ContDiff Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization (lineChart lineTau)

theorem conj_coeff_lineSeedPoly (τ : ℂ) (n : ℕ) (m : Fin 3 →₀ ℕ) :
    conj (((C τ * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) ^ n).coeff m) =
      (((C (conj τ) * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) ^ n).coeff m) := by
  have h : MvPolynomial.map (starRingEnd ℂ) ((C τ * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) ^ n) =
      (C (conj τ) * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) ^ n := by
    simp [map_pow, map_sub, map_mul]
  rw [← h, MvPolynomial.coeff_map]

/-- **The antiholomorphic real entry at a face point.** The complex conjugate of the real intertwining integral `Tinf` of the
seed `h` is `+2πi/(n+1) = conj c_∞` times the conjugate line seed. -/
theorem Tinf_conj_eq_lineSeed (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im}) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) {x : Face} (hx : x ∈ faceSet)
    (p q : Fin 4) (m : Fin 3 →₀ ℕ) :
    conj (Tinf n h x p q m) = (2 * Real.pi * Complex.I / ((n : ℂ) + 1)) *
      (conj (h (lineTau (lineChart (gx x * (gx x).transpose)))) * conj (lineWedge x p q) *
        ((C (conj (lineTau (lineChart (gx x * (gx x).transpose)))) * X 2 - X 1 :
          MvPolynomial (Fin 3) ℂ) ^ n).coeff m) := by
  rw [Tinf_eq_lineSeed n hn h hh M hM hx p q m]
  simp only [map_mul, conj_coeff_lineSeedPoly]
  congr 1
  simp only [map_div₀, map_mul, map_neg, map_add, map_one, map_natCast, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I]
  ring

end TernaryPeriodPolynomials.Argument.EisensteinClass

end
