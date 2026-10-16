module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Energy.CurrentDivergence
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Contraction
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Exterior

@[expose] public section



/-!
# The group-free pointwise inputs of the coercivity estimate

Formalized by Claude Sonnet 5.5.

The estimate of Proposition C.1 rests on four facts about forms at a single point `x` of the
positive cone.  None involves a discrete group, so they are stated once, for forms of degree
`k + 1` with values in the polynomial coefficients `Coefficients n`, and are proved in
`Assembly/Degrees.lean` from the modules of `Revision/Proofs/Coercivity*`:

* `SymmetricAdjoint n k` -- the zero-order symmetric exterior derivative `S↑ : (k)-forms → (k+1)-forms`
  and the symmetric contraction `S↓ : (k+1)-forms → (k)-forms` are adjoint for the pointwise metric;
* `PositiveCoercive n k c` / `BottomCoercive n c` -- `‖S↑ a‖² + ‖S↓ a‖² ≥ c ‖a‖²` for
  `(k+1)`-forms, respectively `‖S↑ a‖² ≥ c ‖a‖²` for `0`-forms;
* `PositiveDivergence n k` / `BottomDivergence n` -- the divergence of the energy current of a smooth
  `(k+1)`-form (respectively `0`-form) `w` is twice the pairing of `w` with the sum of the two mixed
  second-order terms `S↓ ∇ w + ∇ S↓ w`.

Here `∇ = covariantExterior` is the covariant exterior derivative, so that the flat exterior
derivative is `∇ + S↑`.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpacePositive
open scoped ContDiff Matrix.Norms.Elementwise

/-- At every point of the positive cone the symmetric exterior derivative `S↑` on `k`-forms and
the symmetric contraction `S↓` on `(k + 1)`-forms are adjoint for the pointwise form metric
`formPairing`. -/
def SymmetricAdjoint (n k : ℕ) : Prop :=
  ∀ x ∈ positiveCoordinates, ∀ (a : FormValue n k) (b : FormValue n (k + 1)),
    formPairing n (k + 1) x (symmetricExterior n k x a) b =
      formPairing n k x a (symmetricContraction n k x b)

/-- Pointwise algebraic coercivity of `(k + 1)`-forms: the sum of the squared pointwise norms of
`S↑ a` and `S↓ a` is at least `c` times that of `a`. -/
def PositiveCoercive (n k : ℕ) (c : ℝ) : Prop :=
  ∀ x ∈ positiveCoordinates, ∀ a : FormValue n (k + 1),
    c * formPairing n (k + 1) x a a ≤
      formPairing n (k + 1 + 1) x (symmetricExterior n (k + 1) x a) (symmetricExterior n (k + 1) x a) +
        formPairing n k x (symmetricContraction n k x a) (symmetricContraction n k x a)

/-- Pointwise algebraic coercivity of `0`-forms: `‖S↑ a‖² ≥ c ‖a‖²` (there is no `S↓`). -/
def BottomCoercive (n : ℕ) (c : ℝ) : Prop :=
  ∀ x ∈ positiveCoordinates, ∀ a : FormValue n 0,
    c * formPairing n 0 x a a ≤
      formPairing n 1 x (symmetricExterior n 0 x a) (symmetricExterior n 0 x a)

/-- Pointwise divergence identity for `(k + 1)`-forms: for smooth `w`, the weighted divergence of
the energy current `energyCurrent n (k + 1) w` is twice the pairing of `w` with
`S↓ (∇ w) + ∇ (S↓ w)`. -/
def PositiveDivergence (n k : ℕ) : Prop :=
  ∀ {w : Coordinates → FormValue n (k + 1)}, ContDiffOn ℝ ∞ w positiveCoordinates →
    ∀ x ∈ positiveCoordinates,
      weightedDivergence (energyCurrent n (k + 1) w) x =
        2 * formPairing n (k + 1) x (w x)
          (symmetricContraction n (k + 1) x (covariantExterior n (k + 1) w x) +
            covariantExterior n k (fun y => symmetricContraction n k y (w y)) x)

/-- Pointwise divergence identity for `0`-forms: the weighted divergence of the energy current of a
smooth `w` is twice the pairing of `w` with `S↓ (∇ w)`. -/
def BottomDivergence (n : ℕ) : Prop :=
  ∀ {w : Coordinates → FormValue n 0}, ContDiffOn ℝ ∞ w positiveCoordinates →
    ∀ x ∈ positiveCoordinates,
      weightedDivergence (energyCurrent n 0 w) x =
        2 * formPairing n 0 x (w x) (symmetricContraction n 0 x (covariantExterior n 0 w x))

/-- The symmetric contraction is linear, so it vanishes on zero. -/
theorem symmetricContraction_zero (n k : ℕ) (x : Coordinates) :
    symmetricContraction n k x (0 : FormValue n (k + 1)) = 0 := by
  rw [← symmetricContractionCLM_apply]
  exact PolynomialFormCoordinates.clm_map_zero _

/-- The pointwise coercivity constant may be decreased. -/
theorem PositiveCoercive.mono {n k : ℕ} {c c' : ℝ} (h : PositiveCoercive n k c) (hc : c' ≤ c) :
    PositiveCoercive n k c' := fun x hx a =>
  (mul_le_mul_of_nonneg_right hc (formPairing_nonneg n (k + 1) x hx a)).trans (h x hx a)

/-- The pointwise coercivity constant may be decreased. -/
theorem BottomCoercive.mono {n : ℕ} {c c' : ℝ} (h : BottomCoercive n c) (hc : c' ≤ c) :
    BottomCoercive n c' := fun x hx a =>
  (mul_le_mul_of_nonneg_right hc (formPairing_nonneg n 0 x hx a)).trans (h x hx a)

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
