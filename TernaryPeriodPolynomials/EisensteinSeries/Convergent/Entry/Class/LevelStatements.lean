module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.StandardConv.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceData
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceData

@[expose] public section


/-!
# The two analytic inputs of the class-level entry comparison (statements only)

`StandardEndpointIntegral n` (**R-c**): for a family `F` of flat sections with a standard continuation `J`
(`IsStandardConvergent`, analytic at the cohomological point), the standard integrand at `s₀ = -3/2` is absolutely
integrable and `J s₀` is its integral (identity theorem on the half plane `-n/2 < Re s`).

`FiniteEntryIdentity D ι ιL F r` (**R-e**): for the Eichler datum `F` (the function with `E.α = eichlerNormal n F`) and the
finite weight `ι` of the plane section (`ι = 1`: spherical; the `P K₁(3)`-indicator: bad plane), the finite
adelic radical integral of the plane coefficient function `v ↦ ι(g_v) · c_F(g_v) · F(x · b_F(g_v))`, with
`g_v = w⁻¹ u(0,v₁; 0,v₂) g`, is `r` times the line coefficient function `c_F^{line}(g) · F(x · b_F^{line}(g))`, pointwise
in `z`, together with the measurability and the local (in `z`) integrable majorant that allow the integral to be
exchanged with the integral over a Gram triangle.  The identity is required only at `g` with `ιL g ≠ 0`, where `ιL`
is the finite weight of the line component compared (the indicator of the good-line orbit for the bad-plane section).

Both are `Prop`-valued definitions; the class-level theorem `classLevel_conditional` takes them as hypotheses.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- **R-c.**  At the cohomological point the standard integral of a flat family with a standard continuation is
absolutely convergent and equals the continuation. -/
def StandardEndpointIntegral (n : ℕ) : Prop :=
  ∀ (D : InducingData n) (F J : ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n),
    (∀ x m, IsFlatSection D (fun s g => (F s x g).val.coeff m)) →
    (∀ x m, IsStandardConvergent n (fun s g => (F s x g).val.coeff m)
      (fun s g => (J s x g).val.coeff m)) →
    (∀ x g m, AnalyticAt ℂ (fun s => (J s x g).val.coeff m) cohomologicalPoint) →
    ∀ x g m,
      Integrable (standardIntegrand (fun s g' => (F s x g').val.coeff m) cohomologicalPoint g)
        radicalMeasure ∧
      (J cohomologicalPoint x g).val.coeff m =
        ∫ u, standardIntegrand (fun s g' => (F s x g').val.coeff m) cohomologicalPoint g u ∂radicalMeasure

/-- The adelic matrix `w⁻¹ u(0, v₁; 0, v₂) g`: the finite part of the standard integrand at the finite radical
coordinate `v` (the real radical coordinate is set to zero; the finite part of the integrand does not see it). -/
def finiteEntryElement (v : FiniteAdeles × FiniteAdeles) (g : AdelicGL) : AdelicGL :=
  weyl⁻¹ * lineUnipotent ((0, v.1) : Adeles) ((0, v.2) : Adeles) * g

/-- **R-e (two-weight form).**  `ι` is the finite weight of the plane section (`ι = 1`: spherical section; the indicator
of `P K₁` at `3`: the bad-plane section) and `ιL` the finite weight of the line component under comparison (`ιL = 1`:
the whole spherical line section; the indicator of the good-line orbit: the good-line component).  At every `g` with
`ιL g ≠ 0` the finite adelic radical integral of the plane coefficient function `v ↦ ι(g_v) · c_F(g_v) · F(x · b_F(g_v))`
is `r` times the line coefficient function `c_F^{line}(g) · F(x · b_F^{line}(g))`, pointwise in `z`, together with the
measurability and the local (in `z`) integrable majorant that allow the integral to be exchanged with the integral over
a Gram triangle.  Off the support of `ιL` nothing is asserted (the integral there is a different local number). -/
def FiniteEntryIdentity {n : ℕ} (D : InducingData n) (ι ιL : AdelicGL → ℂ) (F : BinaryAdelicGL → ℂ → ℂ)
    (r : ℂ) : Prop :=
  ∀ g : AdelicGL, ιL g ≠ 0 → ∀ x : BinaryAdelicGL,
    Measurable (fun w : (FiniteAdeles × FiniteAdeles) × {z : ℂ // 0 < z.im} =>
      ι (finiteEntryElement w.1 g) *
        (cF D (finiteEntryElement w.1 g) * F (x * bF (finiteEntryElement w.1 g)) w.2.1)) ∧
    (∀ Z : Set ℂ, IsCompact Z → Z ⊆ {z : ℂ | 0 < z.im} →
      ∃ φ : FiniteAdeles × FiniteAdeles → ℝ, Integrable φ (finiteMeasure.prod finiteMeasure) ∧
        ∀ v, ∀ z ∈ Z, ‖ι (finiteEntryElement v g) *
          (cF D (finiteEntryElement v g) * F (x * bF (finiteEntryElement v g)) z)‖ ≤ φ v) ∧
    (∀ z : ℂ, 0 < z.im →
      ∫ v, ι (finiteEntryElement v g) *
          (cF D (finiteEntryElement v g) * F (x * bF (finiteEntryElement v g)) z)
          ∂(finiteMeasure.prod finiteMeasure) =
        r * (cFLine D g * F (x * bFLine g) z))

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
