module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.Integral
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.Printed

@[expose] public section


/-!
# (C), step 11: the printed intertwiner computes the line row of the classical series (standard cusp)

Formalized by Claude Sonnet 5.5.

* `printed_intertwiner_eval`: the literal integral `∫_{𝔸²} φ(w₀⁻¹u(s,t)) ds dt` of the adelic induced section `φ` of the seed of
  `f ∈ S_{n+3}(Γ₂(N))` is absolutely convergent and equals the explicit radical-average coefficient `lineA1K`.
* `printed_intertwiner_orbit_sum`, `printed_intertwiner_Yn`: the orbit-seed sum and the `Yⁿ`-coefficient at `(0, 2)` as the explicit
  absolutely convergent series `seriesPos`, `seriesNeg`.
* `printedCoeff_eq_integral`: the coordinates of `printedForm` (whose class is the line row `r_Q ℰ_P` of the series at the standard cusp,
  `seriesLineCusp_printed`) are these integrals.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open MvPolynomial ComplexConjugate
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.EisensteinDual TernaryPeriodPolynomials.Argument.GammaNFaces

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable {N : ℕ} [NeZero N] {n : ℕ} {f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)}

/-- **The printed intertwiner `∫_{𝔸²} φ(w₀⁻¹u(s,t)) ds dt` of the adelic induced section is the orbit sum `lineA1K`.**
Absolutely convergent for `N ≥ 3`, `n ≥ 4`; Haar measure `radicalMeasure` (Lebesgue × `vol(Ẑ) = 1`). -/
theorem printed_intertwiner_eval (hN : 3 ≤ N) (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) :
    Integrable (printedIntegrand N n f x p q m 1) radicalMeasure ∧
    ∫ u, printedIntegrand N n f x p q m 1 u ∂radicalMeasure = lineA1K N 1 n f false x p q m := by
  have e : printedIntegrand N n f x p q m 1 = fun u => Fz N n f x p q m (radicalEquiv u) :=
    funext (printedIntegrand_one N n f x p q m)
  obtain ⟨hI, hE⟩ := Fz_integral (f := f) hN hn hx p q m
  rw [e]
  refine ⟨(radical_integrable_iff (Fz N n f x p q m)).2 hI, ?_⟩
  rw [radical_integral_eq (Fz N n f x p q m), hE]
  unfold lineA1K
  refine tsum_congr fun o => ?_
  simp [cxL, phiO, orbCoset]

/-- **The congruence-cell form of the integral**: the sum over the free orbits `o` of (volume `N⁻²` of the congruence cell)
times (the real integral over `ℝ²` of the orbit summand at the shifted point). -/
theorem printed_intertwiner_cells (hN : 3 ≤ N) (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) :
    ∫ u, printedIntegrand N n f x p q m 1 u ∂radicalMeasure =
      ∑' o : FreeOrb N, ((N : ℂ) ^ 2)⁻¹ * ∫ w, phiO N n f x p q m o (shiftV (orbPt N o) w) := by
  rw [(printed_intertwiner_eval hN hn hx p q m).2]
  unfold lineA1K
  refine tsum_congr fun o => ?_
  have := integral_phiO N n f (x := x) p q m o
  rw [integral_shiftV (orbPt N o) (phiO N n f x p q m o)]
  simpa [cxL, phiO, orbCoset] using this

/-- **The printed integral as the explicit orbit-seed sum.** -/
theorem printed_intertwiner_orbit_sum (hN : 3 ≤ N) (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) :
    ∫ u, printedIntegrand N n f x p q m 1 u ∂radicalMeasure = ((N : ℂ) ^ 2)⁻¹ * ∑' o : OrbIdx N 1,
      cx false (cx (orbitSign N 1 (Quotient.out o.1))
        (cinf n * (orbitSeed N 1 n f (Quotient.out o.1) ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) *
          lineWedge x p q * ((C ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) * X 2 - X 1 :
            MvPolynomial (Fin 3) ℂ) ^ n).coeff m))) := by
  rw [(printed_intertwiner_eval hN hn hx p q m).2]
  exact lineA1K_printed N 1 n f (by omega) false hx p q m

/-- **The `Yⁿ` coefficient at `(0, 2)` of the printed integral** is `N⁻²((-1)ⁿ (c_∞ S₊(τ_x) + conj c_∞ · conj S₋(τ_x)))`. -/
theorem printed_intertwiner_Yn (hN : 3 ≤ N) (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) :
    ∫ u, printedIntegrand N n f x 0 2 (Finsupp.single 1 n) 1 u ∂radicalMeasure = ((N : ℂ) ^ 2)⁻¹ *
      ((-1) ^ n * (cinf n * seriesPos N 1 n f ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) +
        conj (cinf n) * conj (seriesNeg N 1 n f ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ))))) := by
  rw [(printed_intertwiner_eval hN hn hx 0 2 _).2, lineA1K_Yn_series N 1 n f hn false hx]
  simp [cx]

/-- **The coordinates of the line row of the series at the standard cusp are the printed integrals**:
`printedForm` (whose class is `r_Q ℰ_P`, `seriesLineCusp_printed`) has `(x; e_p, e_q)`, `m`-coordinate `∫_{𝔸²} φ(w₀⁻¹u(s,t))`. -/
theorem printedCoeff_eq_integral (hN : 3 ≤ N) (hn : 4 ≤ n) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) :
    printedCoeff N n f hn false 1 x p q m = ∫ u, printedIntegrand N n f x p q m 1 u ∂radicalMeasure := by
  rw [(printed_intertwiner_eval hN hn hx p q m).2]
  exact lineAvgK_coeff N 1 n f false hn hx p q m

/-- **The line row `r_Q ℰ_P` of the classical holomorphic series at the standard cusp, with the literal printed integrals.**
The named element `Tξ ∈ 𝒞_Q(E)` of `seriesLineCusp` is, through the inverse edge, the transport of the class of `printedForm`, and
the coordinates of `printedForm` are the absolutely convergent integrals `∫_{𝔸²} φ(w₀⁻¹u(s,t)) ds dt` of the adelic induced section. -/
theorem rLine_series_integral (hN : 3 ≤ N) (hn : 4 ≤ n) :
    lineFaceCuspidalEmbedding N 1 n (seriesLineCusp N n hN hn f 1 1 false) =
      (groupCohomology.map (lineAtHom N 1) (lineAtMor N 1 n) 2).hom
        (cxGen (rhoQ N n) (rhoQC N n) (fun _ _ => rfl)
          (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action (rhoQ N n)
            (printedForm N n f hn false 1))) ∧
    ∀ x ∈ faceSet, ∀ (p q : Fin 4) (m : Fin 3 →₀ ℕ),
      Integrable (printedIntegrand N n f x p q m 1) radicalMeasure ∧
      printedCoeff N n f hn false 1 x p q m = ∫ u, printedIntegrand N n f x p q m 1 u ∂radicalMeasure := by
  refine ⟨?_, fun x hx p q m => ⟨(printed_intertwiner_eval hN hn hx p q m).1, printedCoeff_eq_integral hN hn hx p q m⟩⟩
  simpa using seriesLineCusp_printed N n f hN hn 1 1 false

end TernaryPeriodPolynomials.Argument.FormClassK
