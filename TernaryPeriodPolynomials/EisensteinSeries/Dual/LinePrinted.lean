module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Values
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.Printed

@[expose] public section


open scoped MatrixGroups
open CategoryTheory
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.FormClassK

/-!
# The dual line-to-plane row `r_P ℰ_Q^∨ = T^∨ η` in printed coordinates

Formalized by Claude Sonnet 5.5.

* `dual_rP_dualClassC`: the complex plane restriction of the dual series `dualClassC` at the plane cusp `h⁻¹Ph` is the `ȷ`-pullback of the named
  element `Tξ = seriesLineCusp (ȷ h) (ȷ h') b ∈ 𝒞_{ȷ(h)⁻¹Qȷ(h)}(E)` (through the inverse Hochschild-Serre edge).  It does not use a map `T`
  on classes, so no canonicity of `T` or `T^∨` is involved.
* `lineAtHom_comp_jRestr`, `facePullC_map_lineAt`: `ȷ`-pullback after the line transport is the pullback along conjugation `p ↦ h p h⁻¹`.
* `cx_resTo_dual`: the complexified real restriction `r_P` of `dualSeriesAtClass_gammaN` is that complex restriction.
* **`dual_rP_printed`**: `r_P ℰ_Q^∨` is the conjugation-pullback of the class of `printedForm` for the cusp `ȷ(h' h⁻¹)`; its coordinates are the printed
  real integrals `Tinf` of the orbit seeds at that cusp, vanishing for `m₀ ≠ 0`, and given at `Yⁿ` by the explicit series.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinDual

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

theorem dual_rP_dualClassC (hN : 3 ≤ N) (hn : 4 ≤ n) (h h' : SL(3, ℤ)) (b : Bool) :
    resToC N n (ρ := dualRhoC N n) (gammaNPAt N h) (gammaNPAt_le N h) (dualClassC N n f hn b h') =
      facePullC (gammaNPAt_le N h) (gammaNQAt_le_N N (jmath h)) (jmath_P_to_Q h) n
        (lineFaceCuspidalEmbedding N (jmath h) n (seriesLineCusp N n hN hn f (jmath h) (jmath h') b)) := by
  unfold dualClassC
  rw [jPullC_res N n (gammaNPAt_le N h) (gammaNQAt_le_N N (jmath h)) (jmath_P_to_Q h), seriesLineCusp_spec]
  rfl



omit [NeZero N] in
theorem jmath_ratio (h h' : SL(3, ℤ)) : jmath h' * (jmath h)⁻¹ = jmath (h' * h⁻¹) := by
  rw [jmath_mul, jmath_inv]

omit [NeZero N] in
/-- `lineAtHom (ȷ h) ∘ ȷ = conjugation by h`: `p ↦ ȷ(ȷ(h) ȷ(p) ȷ(h)⁻¹) = h p h⁻¹`. -/
theorem lineAtHom_comp_jRestr (h : SL(3, ℤ)) :
    (lineAtHom N (jmath h)).comp (jRestr (gammaNPAt N h) (gammaNQAt N (jmath h)) (jmath_P_to_Q h)) =
      (conjP N h).toMonoidHom := by
  refine MonoidHom.ext fun p => Subtype.ext ?_
  change jmath (jmath h * jmath p.1 * (jmath h)⁻¹) = h * p.1 * h⁻¹
  rw [← jmath_inv, ← jmath_mul, ← jmath_mul, jmath_jmath]

/-- The coefficient morphism of the dual plane row: `lineAtMor (ȷ h)` followed by the `ȷ`-pullback of coefficients. -/
def dualPlaneMor (h : SL(3, ℤ)) :
    Rep.res ((lineAtHom N (jmath h)).comp (jRestr (gammaNPAt N h) (gammaNQAt N (jmath h)) (jmath_P_to_Q h)))
        (Rep.of (rhoQC N n)) ⟶ Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNPAt_le N h))) :=
  (Rep.resFunctor (jRestr (gammaNPAt N h) (gammaNQAt N (jmath h)) (jmath_P_to_Q h))).map (lineAtMor N (jmath h) n) ≫
    resMorK (jRestr (gammaNPAt N h) (gammaNQAt N (jmath h)) (jmath_P_to_Q h))
      ((dualRhoC N n).comp (Subgroup.inclusion (gammaNPAt_le N h)))
      ((gammaRhoC (gammaN N) n).comp (Subgroup.inclusion (gammaNQAt_le_N N (jmath h))))
      (facePullC_compat (gammaNPAt_le N h) (gammaNQAt_le_N N (jmath h)) (jmath_P_to_Q h))

theorem facePullC_map_lineAt (h : SL(3, ℤ)) (y : groupCohomology.H2 (Rep.of (rhoQC N n))) :
    facePullC (gammaNPAt_le N h) (gammaNQAt_le_N N (jmath h)) (jmath_P_to_Q h) n
        ((groupCohomology.map (lineAtHom N (jmath h)) (lineAtMor N (jmath h) n) 2).hom y) =
      (groupCohomology.map ((lineAtHom N (jmath h)).comp
        (jRestr (gammaNPAt N h) (gammaNQAt N (jmath h)) (jmath_P_to_Q h))) (dualPlaneMor N n h) 2).hom y := by
  unfold dualPlaneMor facePullC
  exact (congrArg (fun m => m.hom y) (groupCohomology.map_comp (lineAtHom N (jmath h))
    (jRestr (gammaNPAt N h) (gammaNQAt N (jmath h)) (jmath_P_to_Q h)) (lineAtMor N (jmath h) n)
    (resMorK (jRestr (gammaNPAt N h) (gammaNQAt N (jmath h)) (jmath_P_to_Q h))
      ((dualRhoC N n).comp (Subgroup.inclusion (gammaNPAt_le N h)))
      ((gammaRhoC (gammaN N) n).comp (Subgroup.inclusion (gammaNQAt_le_N N (jmath h))))
      (facePullC_compat (gammaNPAt_le N h) (gammaNQAt_le_N N (jmath h)) (jmath_P_to_Q h))) 2)).symm



theorem cx_resTo_dual (hn : 4 ≤ n) (h h' : SL(3, ℤ)) (b : Bool) :
    cxFaceDual (gammaNPAt N h) (gammaNPAt_le N h) n
        (resTo (gammaNPAt N h) (gammaNPAt_le N h) (dualRhoN N n) (dualSeriesAtClass_gammaN N n f hn b h')) =
      resToC N n (ρ := dualRhoC N n) (gammaNPAt N h) (gammaNPAt_le N h) (dualClassC N n f hn b h') := by
  rw [dualClassC_eq_cxGen]
  have key := cxGen_map ((dualRhoN N n).comp (Subgroup.inclusion (gammaNPAt_le N h)))
    ((dualRhoC N n).comp (Subgroup.inclusion (gammaNPAt_le N h))) (fun _ _ => rfl) (dualRhoN N n) (dualRhoC N n)
    (fun _ _ => rfl) (Subgroup.inclusion (gammaNPAt_le N h)) (fun _ => rfl) (fun _ => rfl)
    (dualSeriesAtClass_gammaN N n f hn b h')
  exact key



open TernaryPoly.SmoothLocalDeRham in
/-- **The dual line-to-plane row, in printed coordinates** (`eq:dualconstantterms`, `r_P ℰ_Q^∨ = T^∨ η`).
For the cusp pair `(h, h')` (plane cusp `h⁻¹Ph` of `E^∨`, dual series attached to the line cusp `h'`), `3 ≤ N`, `4 ≤ n`:
the complex plane restriction of the dual series is the pullback, along `p ↦ h p h⁻¹ : Γ_{h⁻¹Ph} → Γ_P`
(`lineAtHom (ȷ h) ∘ ȷ = conjP h`), of the de Rham class of `printedForm` for the cusp `ȷ(h' h⁻¹)`; its coordinates are the printed
real integrals `Tinf` of the orbit seeds at that cusp. -/
theorem dual_rP_printed (hN : 3 ≤ N) (hn : 4 ≤ n) (h h' : SL(3, ℤ)) (b : Bool) :
    resToC N n (ρ := dualRhoC N n) (gammaNPAt N h) (gammaNPAt_le N h) (dualClassC N n f hn b h') =
      (groupCohomology.map ((lineAtHom N (jmath h)).comp
        (jRestr (gammaNPAt N h) (gammaNQAt N (jmath h)) (jmath_P_to_Q h))) (dualPlaneMor N n h) 2).hom
        (cxGen (rhoQ N n) (rhoQC N n) (fun _ _ => rfl)
          (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action (rhoQ N n)
            (printedForm N n f hn b (jmath (h' * h⁻¹))))) ∧
    (∀ x ∈ faceSet, ∀ (p q : Fin 4) (m : Fin 3 →₀ ℕ),
      printedCoeff N n f hn b (jmath (h' * h⁻¹)) x p q m = ((N : ℂ) ^ 2)⁻¹ * ∑' o : OrbIdx N (jmath (h' * h⁻¹)),
        cx b (cx (orbitSign N (jmath (h' * h⁻¹)) (Quotient.out o.1))
          (cinf n * (orbitSeed N (jmath (h' * h⁻¹)) n f (Quotient.out o.1) ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) *
            lineWedge x p q * ((MvPolynomial.C ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) * MvPolynomial.X 2 - MvPolynomial.X 1 :
              MvPolynomial (Fin 3) ℂ) ^ n).coeff m)))) ∧
    (∀ x ∈ faceSet, ∀ (p q : Fin 4) (m : Fin 3 →₀ ℕ), m 0 ≠ 0 →
      printedCoeff N n f hn b (jmath (h' * h⁻¹)) x p q m = 0) ∧
    (∀ x ∈ faceSet, printedCoeff N n f hn b (jmath (h' * h⁻¹)) x 0 2 (Finsupp.single 1 n) = ((N : ℂ) ^ 2)⁻¹ *
      cx b ((-1) ^ n * (cinf n * seriesPos N (jmath (h' * h⁻¹)) n f ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)) +
        (starRingEnd ℂ) (cinf n) * (starRingEnd ℂ)
          (seriesNeg N (jmath (h' * h⁻¹)) n f ((-(x 2) : ℝ) + Complex.I * (x 3 : ℝ)))))) := by
  obtain ⟨h1, h2, h3, h4⟩ := rLine_series_printed N n f hN hn (jmath h) (jmath h') b
  rw [jmath_ratio] at h1 h2 h3 h4
  refine ⟨?_, h2, h3, h4⟩
  rw [dual_rP_dualClassC N n f hN hn h h' b, h1]
  exact facePullC_map_lineAt N n h _

end TernaryPeriodPolynomials.Argument.EisensteinDual
