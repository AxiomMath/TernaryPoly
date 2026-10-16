module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.ClassLevel

@[expose] public section


/-!
# The sign and normalization dictionary of the archimedean/finite entry

Three scalars are in play.

* `r` — the **bare** coefficient of `FiniteEntryIdentity D ι ιL F r`: the finite adelic radical integral of the plane
  coefficient function `ι · c_F · F(x b_F)` equals `r · c_F^{line} F(x b_F^{line})`.  For the spherical section
  `r = ∏_p (local Euler factors)`, the Euler factor at `3` included; for the bad-plane/good-line pair it is `(1/9)` times
  the `3`-omitted `L`-ratio `L^{(3)}(h,k-2)/L^{(3)}(h,k-1)` (paper).
* `c_∞ = -2πi/(n+1)` — the real entry (`tcommute`: `T_∞ ω_h = c_∞ σ_h` for the **same** function `h` in the plane seed `ω_h`
  and the line seed `σ_h`).
* `entryScalar n r = (-r)·c_∞` — the scalar of the class-level comparison `T[ι·planeSource] = entryScalar n r ·
  [ιL·lineSource]` (`classLevel_of_Ra`).

**Where the minus sign comes from.**  The library's two sources are the integral cochains of the two seeds (bridge
theorems `coeff_planeSourceAt_bridge`, `coeff_lineSourceAt_bridge`) with the data
`h_plane = (-1)ⁿ (n+1) · c_F/2 · F` and `h_line = (-1)^{n+1} (n+1) · c_F^{line}/2 · F`: for the *same* `F` the line datum carries the
opposite sign (`lineHolData_eq_neg`).  The paper's pair `(ω_h, σ_h)` uses the same `h` on both sides, so the finite
integral, which turns the plane datum of `F` into `r` times the plane-sign datum of the line `F`, produces
`r · c_∞` times the *paper-sign* line section `σ_{h_plane-sign} = -σ_{h_line}`, i.e. `-` the library line source:
`∫ ι cΩ(w⁻¹ u g) du = (r c_∞) · (-cΣ(g))` (`standardIntegral_cOmega_paperSign`).  Consequently the printed scalar
`-2πi/(9(n+1)) · L^{(3)}(h,k-2)/L^{(3)}(h,k-1)` equals `r c_∞` with `r = value/9` (`SphericalEntryData.printedScalar_eq`),
and `entryScalar n (value/9)` is exactly **minus** the printed scalar (`SphericalEntryData.entryScalar_rPrint`, in
`Entry/REValue`): the library's line source is `-` the paper's line section.  The sign is
a normalization of the (library) line source, not a contradiction; nonvanishing and the identification of the zero
set are unaffected.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SourceConstruction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- The plane-sign line datum `(-1)ⁿ (n+1) · c_F^{line}/2 · F(x b_F^{line})`, the line datum of the paper's pair
`(ω_h, σ_h)` (the same sign as the plane datum `planeHolData`). -/
def lineHolDataPaper (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (g : AdelicGL)
    (x : BinaryAdelicGL) (z : ℂ) : ℂ :=
  (-1) ^ n * ((n + 1 : ℕ) : ℂ) * (cFLine D g * 2⁻¹ * F (x * bFLine g) z)

/-- **The library line datum is minus the paper-sign line datum.** -/
theorem lineHolData_eq_neg (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (g : AdelicGL)
    (x : BinaryAdelicGL) (z : ℂ) : lineHolData n D F g x z = -lineHolDataPaper n D F g x z := by
  unfold lineHolData lineHolDataPaper
  rw [pow_succ]
  ring

/-- `entryScalar n r = -(r · c_∞)`. -/
theorem entryScalar_eq_neg (n : ℕ) (r : ℂ) :
    entryScalar n r = -(r * (-2 * Real.pi * Complex.I / ((n : ℂ) + 1))) := by
  unfold entryScalar
  ring

open MeasureTheory GeneralEisenstein.Adelic in
/-- **The standard integral of the plane integral cochain in the paper's sign**: `r · c_∞` times *minus* the library
line integral cochain (= the line seed `σ_h` with the plane-sign datum). -/
theorem standardIntegral_cOmega_paperSign (n : ℕ) (hn : 3 ≤ n) (D : InducingData n) (ι ιL : AdelicGL → ℂ)
    (hι : ∀ g g' : AdelicGL, finiteGroup g = finiteGroup g' → ι g = ι g') (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ x, DifferentiableOn ℂ (F x) {z : ℂ | 0 < z.im})
    (decay : ∀ x, ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖F x z‖ ^ 2 * z.im ^ (n + 3) ≤ M)
    (r : ℂ) (hRe : FiniteEntryIdentity D ι ιL F r) (y : Fin 3 → RealGL3) (g : AdelicGL) (hg : ιL g ≠ 0)
    (κ : Fin 3 →₀ ℕ)
    (hint : Integrable (fun u : Adeles × Adeles =>
      ι (weyl⁻¹ * lineUnipotent u.1 u.2 * g) * cOmegaCoeff n D F y (weyl⁻¹ * lineUnipotent u.1 u.2 * g) κ)
      radicalMeasure) :
    ∫ u : Adeles × Adeles, ι (weyl⁻¹ * lineUnipotent u.1 u.2 * g) *
      cOmegaCoeff n D F y (weyl⁻¹ * lineUnipotent u.1 u.2 * g) κ ∂radicalMeasure =
      (r * (-2 * Real.pi * Complex.I / ((n : ℂ) + 1))) * (-(cSigmaCoeff n D F y g κ)) := by
  rw [standardIntegral_cOmega n hn D ι ιL hι F holomorphic decay r hRe y g hg κ hint]
  ring

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
