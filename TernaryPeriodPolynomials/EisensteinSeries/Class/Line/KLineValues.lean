module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KLineTangent
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBridgeC

@[expose] public section


/-!
# The explicit line seed on the face: wedge table and the `Y`-coordinate

Paper: Appendix C.5.

With `lineTangent g_x V_e = (-e₁, -e₀, -e₂, e₃, *)` (`lineTangent_gx_values`) the wedge scalar of the bridge
`Tinf_eq_lineSeed` is explicit: with `τ_x = -ξ + iη`,
`W(0,2) = 1`, `W(0,3) = -i`, `W(1,2) = τ_x`, `W(1,3) = -iτ_x`, `W(0,1) = W(2,3) = 0`
(`lineWedge_02`, ...), and the polynomial factor `(τ_x Z - Y)ⁿ` has no `X`: its coefficients with `m₀ ≠ 0` vanish
(`coeff_lineLin_pow_of_ne`) and the `Yⁿ`-coefficient is `(-1)ⁿ` (`coeff_lineLin_pow_Yn`).

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial
open scoped MatrixGroups ContDiff Matrix
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.GammaNFaces
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinDual
  TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
  TernaryPeriodPolynomials.Argument.SeedC3.Psi
open TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization (lineChart lineTangent lineTau)

section Values

/-- **The line-chart tangents of the Maurer-Cartan directions**: `(-e₁, -e₀, -e₂, e₃)`. -/
theorem lineTangent_gx_values {x : Face} (hx : x ∈ faceSet) (e : Face) :
    lineTangent (gx x) (Vgx x e) 0 = -(e 1) ∧ lineTangent (gx x) (Vgx x e) 1 = -(e 0) ∧
    lineTangent (gx x) (Vgx x e) 2 = -(e 2) ∧ lineTangent (gx x) (Vgx x e) 3 = e 3 := by
  have key : ∀ (a : Fin 5) (ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) (i : Fin 4) (s : ℝ),
      (∀ y : Face, y ∈ faceSet → lineChart (gx y * (gx y).transpose) a = s * y i) →
      lineTangent (gx x) (Vgx x e) a = s * e i := by
    intro a ha i s hs
    rw [lineTangent_gx_eq hx e a ha]
    have hev : (fun ε : ℝ => lineChart (gx (x + ε • e) * (gx (x + ε • e)).transpose) a)
        =ᶠ[nhds (0 : ℝ)] fun ε => s * (x + ε • e) i := by
      filter_upwards [eventually_mem_face hx e] with ε hε using hs _ hε
    rw [hev.deriv_eq]
    have : HasDerivAt (fun ε : ℝ => s * (x + ε • e) i) (s * e i) 0 := by
      have h1 : HasDerivAt (fun ε : ℝ => (x + ε • e) i) (e i) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (e i)).const_add (x i)
      exact h1.const_mul s
    exact this.deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := key 0 (Or.inl rfl) 1 (-1) (fun y hy => by rw [(lineChart_gx_values hy).1]; ring)
    simpa using this
  · have := key 1 (Or.inr (Or.inl rfl)) 0 (-1) (fun y hy => by rw [(lineChart_gx_values hy).2.1]; ring)
    simpa using this
  · have := key 2 (Or.inr (Or.inr (Or.inl rfl))) 2 (-1) (fun y hy => by rw [(lineChart_gx_values hy).2.2.1]; ring)
    simpa using this
  · have := key 3 (Or.inr (Or.inr (Or.inr rfl))) 3 1 (fun y hy => by rw [(lineChart_gx_values hy).2.2.2]; ring)
    simpa using this


theorem lineTau_gx {x : Face} (hx : x ∈ faceSet) :
    lineTau (lineChart (gx x * (gx x).transpose)) = (-(x 2) : ℝ) + Complex.I * (x 3 : ℝ) := by
  unfold lineTau
  rw [(lineChart_gx_values hx).2.2.1, (lineChart_gx_values hx).2.2.2]

theorem lineWedge_eq {x : Face} (hx : x ∈ faceSet) (p q : Fin 4) :
    lineWedge x p q =
      (((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) * ((-(Pi.single p (1 : ℝ) : Face) 1 : ℝ) : ℂ) +
          ((-(Pi.single p (1 : ℝ) : Face) 0 : ℝ) : ℂ)) *
        (((-(Pi.single q (1 : ℝ) : Face) 2 : ℝ) : ℂ) + Complex.I * (((Pi.single q (1 : ℝ) : Face) 3 : ℝ) : ℂ)) -
      (((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) * ((-(Pi.single q (1 : ℝ) : Face) 1 : ℝ) : ℂ) +
          ((-(Pi.single q (1 : ℝ) : Face) 0 : ℝ) : ℂ)) *
        (((-(Pi.single p (1 : ℝ) : Face) 2 : ℝ) : ℂ) + Complex.I * (((Pi.single p (1 : ℝ) : Face) 3 : ℝ) : ℂ)) := by
  unfold lineWedge
  rw [lineTau_gx hx]
  have hp := lineTangent_gx_values hx (Pi.single p 1)
  have hq := lineTangent_gx_values hx (Pi.single q 1)
  simp only [TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry.lineBeta,
    TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry.lineDTauOf, hp.1, hp.2.1, hp.2.2.1,
    hp.2.2.2, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2]

theorem lineWedge_02 {x : Face} (hx : x ∈ faceSet) : lineWedge x 0 2 = 1 := by
  rw [lineWedge_eq hx]; simp
theorem lineWedge_03 {x : Face} (hx : x ∈ faceSet) : lineWedge x 0 3 = -Complex.I := by
  rw [lineWedge_eq hx]; simp
theorem lineWedge_12 {x : Face} (hx : x ∈ faceSet) :
    lineWedge x 1 2 = (-(x 2) : ℝ) + Complex.I * (x 3 : ℝ) := by
  rw [lineWedge_eq hx]; simp
theorem lineWedge_13 {x : Face} (hx : x ∈ faceSet) :
    lineWedge x 1 3 = -Complex.I * ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) := by
  rw [lineWedge_eq hx]; simp; ring
theorem lineWedge_01 {x : Face} (hx : x ∈ faceSet) : lineWedge x 0 1 = 0 := by
  rw [lineWedge_eq hx]; simp
theorem lineWedge_23 {x : Face} (hx : x ∈ faceSet) : lineWedge x 2 3 = 0 := by
  rw [lineWedge_eq hx]; simp

end Values

section Poly

theorem lineLin_isHomogeneous (τ : ℂ) (n : ℕ) :
    ((C τ * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) ^ n).IsHomogeneous n := by
  have h : (C τ * X 2 - X 1 : MvPolynomial (Fin 3) ℂ).IsHomogeneous 1 :=
    ((isHomogeneous_C_mul_X τ 2).sub (isHomogeneous_X ℂ 1))
  simpa using h.pow n

/-- **The `m₀ ≥ 1` vanishing** (named, valid at every face point): the polynomial factor `(τZ - Y)ⁿ` of the line
seed does not involve `X`, so its coefficient at any `m` with `m 0 ≠ 0` is zero. -/
theorem coeff_lineLin_pow_of_ne (τ : ℂ) (n : ℕ) (m : Fin 3 →₀ ℕ) (hm : m 0 ≠ 0) :
    ((C τ * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) ^ n).coeff m = 0 := by
  by_contra hne
  have hmem : m ∈ ((C τ * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) ^ n).support :=
    MvPolynomial.mem_support_iff.2 hne
  have h1 := MvPolynomial.monomial_le_degreeOf (0 : Fin 3) hmem
  have h2 : MvPolynomial.degreeOf 0 (C τ * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) = 0 := by
    have a1 := MvPolynomial.degreeOf_sub_le (0 : Fin 3) (C τ * X 2 : MvPolynomial (Fin 3) ℂ) (X 1)
    have a2 := MvPolynomial.degreeOf_C_mul_le (X 2 : MvPolynomial (Fin 3) ℂ) 0 τ
    have a3 : MvPolynomial.degreeOf 0 (X 2 : MvPolynomial (Fin 3) ℂ) = 0 :=
      MvPolynomial.degreeOf_X_of_ne (by decide)
    have a4 : MvPolynomial.degreeOf 0 (X 1 : MvPolynomial (Fin 3) ℂ) = 0 :=
      MvPolynomial.degreeOf_X_of_ne (by decide)
    omega
  have h3 := MvPolynomial.degreeOf_pow_le (0 : Fin 3) (C τ * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) n
  rw [h2] at h3
  have : m 0 = 0 := by simpa using h1.trans h3
  exact hm this

theorem coeff_lineLin_pow_Yn (τ : ℂ) (n : ℕ) :
    ((C τ * X 2 - X 1 : MvPolynomial (Fin 3) ℂ) ^ n).coeff (Finsupp.single 1 n) = (-1) ^ n := by
  rw [coeff_single_eq_eval (lineLin_isHomogeneous τ n)]
  simp

end Poly

end TernaryPeriodPolynomials.Argument.EisensteinClass
