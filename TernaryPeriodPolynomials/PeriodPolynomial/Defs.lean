module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Multiplicativity
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section


/-!
# Classical cusp forms, Hecke eigenforms and period polynomials (Sections 1, 2.3 and 7.2)

Paper:.

* `S_k = CuspForm levelOne k` is Mathlib's space of level-one cusp forms, with
  `levelOne = SL₂(ℤ)` inside `GL₂(ℝ)`.
* `a_h(m)` is the `m`-th coefficient of Mathlib's `q`-expansion.
* The prime Hecke operator is the paper's
  `(T_p h)(τ) = p^{k-1} h(pτ) + p⁻¹ ∑_{b<p} h((τ+b)/p)`, i.e. the project's
  `HasPrimeHeckeRelations` (displayed formula after `T_m h` in Section 2.3).
* The period polynomial is `r_h(X,Y) = ∫_0^{i∞} h(τ)(τY - X)^n dτ`
  (equation `eq:analytic-period`), written through the moments
  `∫_0^∞ h(iy) y^j dy` along `τ = iy`.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument

/-- `SL₂(ℤ)` as a subgroup of `GL₂(ℝ)`. -/
abbrev levelOne : Subgroup (GL (Fin 2) ℝ) :=
  TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne

/-- The Fourier coefficient `a_h(m)` of a level-one cusp form. -/
def fourierCoeff {k : ℤ} (h : CuspForm levelOne k) (m : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion levelOne.strictWidthInfty h).coeff m

/-- A normalized level-one cusp eigenform: `a_h(1) = 1` and `h` is an eigenvector of every
prime Hecke operator `T_p` (Section 2.3). -/
def IsNormalizedEigenform {k : ℤ} (h : CuspForm levelOne k) : Prop :=
  fourierCoeff h 1 = 1 ∧ ∃ eigenvalue : Nat.Primes → ℂ,
    TernaryPeriodPolynomials.SphericalDetection.Helpers.HasPrimeHeckeRelations k h
      eigenvalue

/-- The value `h(iy)` for `y > 0`, extended by zero. -/
def imaginaryAxisValue {k : ℤ} (h : CuspForm levelOne k) (y : ℝ) : ℂ :=
  if hy : 0 < y then h ⟨Complex.I * y, by simpa using hy⟩ else 0

/-- The moment `∫_0^∞ h(iy) y^j dy`, the completed value `Λ(h, j+1)`. -/
def periodMoment {k : ℤ} (h : CuspForm levelOne k) (j : ℕ) : ℂ :=
  ∫ y in Set.Ioi (0 : ℝ), imaginaryAxisValue h y * (y : ℂ) ^ j

/-- The period polynomial `r_h(X,Y) = ∫_0^{i∞} h(τ)(τY - X)^n dτ`: along `τ = iy` its
coefficient of `X^{n-j} Y^j` is `binom(n,j) (-1)^{n-j} i^{j+1} ∫_0^∞ h(iy) y^j dy`
(equation `eq:period-critical-coefficients`). -/
def periodPolynomial (n : ℕ) {k : ℤ} (h : CuspForm levelOne k) : MvPolynomial (Fin 2) ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    C ((n.choose j : ℂ) * (-1) ^ (n - j) * Complex.I ^ (j + 1) * periodMoment h j) *
      X 0 ^ (n - j) * X 1 ^ j

/-- The odd part in `X`, `r_h^{odd}(X,Y) = (r_h(X,Y) - r_h(-X,Y))/2`. -/
def oddPeriodPart (n : ℕ) {k : ℤ} (h : CuspForm levelOne k) : MvPolynomial (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • (periodPolynomial n h - bind₁ ![-X 0, X 1] (periodPolynomial n h))

/-- The even part in `X`, `r_h^{ev}(X,Y) = (r_h(X,Y) + r_h(-X,Y))/2`. -/
def evenPeriodPart (n : ℕ) {k : ℤ} (h : CuspForm levelOne k) : MvPolynomial (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • (periodPolynomial n h + bind₁ ![-X 0, X 1] (periodPolynomial n h))

/-- The axis-normalized even part `r_h^{ev,0} = r_h^{ev} - r_h^{ev}(1,0)(X^n - Y^n)`
(equation `eq:even-period-normalization`). -/
def normalizedEvenPeriodPart (n : ℕ) {k : ℤ} (h : CuspForm levelOne k) :
    MvPolynomial (Fin 2) ℂ :=
  evenPeriodPart n h - C (eval ![1, 0] (evenPeriodPart n h)) * (X 0 ^ n - X 1 ^ n)

end TernaryPeriodPolynomials.Argument
