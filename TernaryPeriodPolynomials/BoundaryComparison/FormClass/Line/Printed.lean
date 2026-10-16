module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.CuspBridge
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.CuspNamed
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KOrbitSplit

@[expose] public section


/-!
# `LinePrinted`: the line row of the classical series as the printed real integrals

Formalized by Claude Sonnet 5.5.

For `h, h' ∈ SL₃(ℤ)` and a seed type `b`, let `k = h' h⁻¹` and `printedForm` the radical average of the standard
line-face pullback of the series `ℰ^b_k` (the form of `lineFaceForm_class_eq_avg`).

* `seriesLineCusp_printed`: the element `Tξ ∈ 𝒞_{h⁻¹Qh}(E)` named by `seriesLineCusp`, mapped by the inverse edge,
  is the transport along `(lineAtHom, lineAtMor)` of the complexified class of `printedForm`.
* `printedForm_coeff`: in the face coordinates `(x; e_p, e_q)` (`e_p = Pi.single p 1 : Face`) its `m`-th coefficient is
  `N⁻² Σ_o cx b (cx (sign o) (c_∞ · seed_o(τ_x) · W(p,q) · coeff_m (τ_x Z - Y)ⁿ))`, the printed real integral
  (`Tinf`) of the orbit seeds, with `τ_x = -x₂ + i x₃`, `W` the explicit wedge table (`lineWedge_02` ...).
* `printedForm_coeff_eq_zero_of_ne`: the coefficients with `m₀ ≠ 0` vanish.
* `printedForm_coeff_Yn`: the `Yⁿ`-coefficient at `(0, 2)` is `N⁻² cx b ((-1)ⁿ (c_∞ S₊(τ_x) + conj c_∞ · conj S₋(τ_x)))`
  with the explicit absolutely convergent orbit-seed series `seriesPos`, `seriesNeg`.
-/

open scoped MatrixGroups ContDiff
open MvPolynomial ComplexConjugate
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- **The radical average of the standard line-face pullback of the series at the cusp `k`**, whose class is that of the
pullback (`lineFaceForm_class_eq_avg`) and whose coordinates are the printed integrals. -/
def printedForm (hn : 4 ≤ n) (b : Bool) (k : SL(3, ℤ)) :=
  (lineTwist N n).avInvT (lineFaceForm N n (planeEisensteinAtInv b (CuspData.ofSL k) (gammaN N) (leviGroup N) n f hn
    (leviInCusp_gammaN N k)))

/-- **The line row of the series, as a class.** `Tξ ∈ 𝒞_{h⁻¹Qh}(E)` (named by `seriesLineCusp`), mapped to
`H²(Γ_{h⁻¹Qh}, E)` by the inverse Hochschild-Serre edge, is the transport of the complexified class of
`printedForm` for the cusp `h' h⁻¹`. -/
theorem seriesLineCusp_printed (hN : 3 ≤ N) (hn : 4 ≤ n) (h h' : SL(3, ℤ)) (b : Bool) :
    lineFaceCuspidalEmbedding N h n (seriesLineCusp N n hN hn f h h' b) =
      (groupCohomology.map (lineAtHom N h) (lineAtMor N h n) 2).hom
        (cxGen (rhoQ N n) (rhoQC N n) (fun _ _ => rfl)
          (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action (rhoQ N n)
            (printedForm N n f hn b (h' * h⁻¹)))) := by
  rw [seriesLineCusp_spec, ← cxGen_eq_complexify]
  refine (rLine_series_cusp N h n f hn b h').trans ?_
  rw [printedForm, ← lineFaceForm_class_eq_avg]

/-- The `m`-th coefficient of `printedForm` at `(x; e_p, e_q)` in the face coordinates (`e_p = Pi.single p 1`). -/
abbrev printedCoeff (hn : 4 ≤ n) (b : Bool) (k : SL(3, ℤ)) (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ) : ℂ :=
  (Coef.toPoly (((((printedForm N n f hn b k) :
          ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action (rhoQ N n)) :
            Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
          ![Pi.single p 1, Pi.single q 1])).coeff m

/-- **The coordinates of the line row**: the printed real integrals of the orbit seeds. -/
theorem printedForm_coeff (hn : 4 ≤ n) (b : Bool) (k : SL(3, ℤ)) {x : Face} (hx : x ∈ faceSet) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) :
    printedCoeff N n f hn b k x p q m = ((N : ℂ) ^ 2)⁻¹ * ∑' o : OrbIdx N k,
      cx b (cx (orbitSign N k (Quotient.out o.1))
        (cinf n * (orbitSeed N k n f (Quotient.out o.1) ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) *
          lineWedge x p q * ((C ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) * X 2 - X 1 :
            MvPolynomial (Fin 3) ℂ) ^ n).coeff m))) :=
  (lineAvgK_coeff N k n f b hn hx p q m).trans (lineA1K_printed N k n f (by omega) b hx p q m)

/-- The coefficients with `m₀ ≠ 0` vanish (the named vanishing of the line seed). -/
theorem printedForm_coeff_eq_zero_of_ne (hn : 4 ≤ n) (b : Bool) (k : SL(3, ℤ)) {x : Face} (hx : x ∈ faceSet)
    (p q : Fin 4) (m : Fin 3 →₀ ℕ) (hm : m 0 ≠ 0) : printedCoeff N n f hn b k x p q m = 0 :=
  (lineAvgK_coeff N k n f b hn hx p q m).trans (lineA1K_eq_zero_of_ne N k n f (by omega) b hx p q m hm)

/-- **The `Yⁿ`-coefficient at `(0, 2)`**: `N⁻² cx b ((-1)ⁿ (c_∞ S₊(τ_x) + conj c_∞ · conj S₋(τ_x)))`, with the
absolutely convergent orbit-seed series `seriesPos`, `seriesNeg` (`summable_orbitSeed`). -/
theorem printedForm_coeff_Yn (hn : 4 ≤ n) (b : Bool) (k : SL(3, ℤ)) {x : Face} (hx : x ∈ faceSet) :
    printedCoeff N n f hn b k x 0 2 (Finsupp.single 1 n) = ((N : ℂ) ^ 2)⁻¹ *
      cx b ((-1) ^ n * (cinf n * seriesPos N k n f ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) +
        conj (cinf n) * conj (seriesNeg N k n f ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ))))) :=
  (lineAvgK_coeff N k n f b hn hx 0 2 _).trans (lineA1K_Yn_series N k n f hn b hx)

/-- **The line row at every line cusp and both seeds, in face coordinates** (target of the glue item): the named
element `Tξ` of `𝒞_{h⁻¹Qh}(E)` is, through the inverse edge, the transport of the class of `printedForm` for the cusp
`h' h⁻¹`, whose coordinates are the printed integrals, vanish for `m₀ ≠ 0`, and are the explicit series at `Yⁿ`. -/
theorem rLine_series_printed (hN : 3 ≤ N) (hn : 4 ≤ n) (h h' : SL(3, ℤ)) (b : Bool) :
    lineFaceCuspidalEmbedding N h n (seriesLineCusp N n hN hn f h h' b) =
      (groupCohomology.map (lineAtHom N h) (lineAtMor N h n) 2).hom
        (cxGen (rhoQ N n) (rhoQC N n) (fun _ _ => rfl)
          (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action (rhoQ N n)
            (printedForm N n f hn b (h' * h⁻¹)))) ∧
    (∀ x ∈ faceSet, ∀ (p q : Fin 4) (m : Fin 3 →₀ ℕ),
      printedCoeff N n f hn b (h' * h⁻¹) x p q m = ((N : ℂ) ^ 2)⁻¹ * ∑' o : OrbIdx N (h' * h⁻¹),
        cx b (cx (orbitSign N (h' * h⁻¹) (Quotient.out o.1))
          (cinf n * (orbitSeed N (h' * h⁻¹) n f (Quotient.out o.1) ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) *
            lineWedge x p q * ((C ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) * X 2 - X 1 :
              MvPolynomial (Fin 3) ℂ) ^ n).coeff m)))) ∧
    (∀ x ∈ faceSet, ∀ (p q : Fin 4) (m : Fin 3 →₀ ℕ), m 0 ≠ 0 →
      printedCoeff N n f hn b (h' * h⁻¹) x p q m = 0) ∧
    (∀ x ∈ faceSet, printedCoeff N n f hn b (h' * h⁻¹) x 0 2 (Finsupp.single 1 n) = ((N : ℂ) ^ 2)⁻¹ *
      cx b ((-1) ^ n * (cinf n * seriesPos N (h' * h⁻¹) n f ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) +
        conj (cinf n) * conj (seriesNeg N (h' * h⁻¹) n f ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)))))) :=
  ⟨seriesLineCusp_printed N n f hN hn h h' b,
    fun _ hx p q m => printedForm_coeff N n f hn b _ hx p q m,
    fun _ hx p q m hm => printedForm_coeff_eq_zero_of_ne N n f hn b _ hx p q m hm,
    fun _ hx => printedForm_coeff_Yn N n f hn b _ hx⟩

end TernaryPeriodPolynomials.Argument.FormClassK
