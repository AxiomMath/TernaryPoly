module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.StandardCusp
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Cuspidal
public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinCuspTerm
public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinConstantTerm

@[expose] public section


open CategoryTheory MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane MatrixGroups ContDiff

/-!
# The dual rows at every line cusp: `r_Q ℰ_Q^∨ = η` for both seeds

Formalized by Claude Sonnet 5.5.

`resTo_cuspFace` identifies the group restriction `resTo (Γ_{h⁻¹Ph})` of the class of the series at a plane cusp
`h'` with the de Rham class of `cuspFaceForm N h`, for every `h` and `h'` (the `eisensteinAtClass_gammaN_cuspFace`; `resTo` and `resMor (inclAt N h)` are the same
map, `inclAt N h` being `Subgroup.inclusion (gammaNPAt_le N h)`).  This generalises `StandardCusp.resTo_standard` (which compares with the `resP`, valid for `h = 1`) to
every cusp.  With the `constant_term_identity_at` / `_at_conj`:

* `resTo_plane_seed`: `r_P ℰ_P(ω_f)` at the plane cusp `h⁻¹ P h` of the series AT that cusp is the transported seed class `cuspSeedClassAt` (both seeds);
* `dualSeriesAtClass_gammaN`: the dual series at the line cusp `h⁻¹ Q h`, `ℰ_Q^∨` = `ȷ^*` of the series at the plane cusp `ȷ(h)`, for the seed of type `b`;
* `dual_rQ_at`: `r_Q ℰ_Q^∨ = η` at every line cusp, `η = ȷ^*(cuspSeedClassAt (ȷ h))`, unconditional for `3 ≤ N`, `4 ≤ n`, both seeds;
* `dual_rQ_at_literal`: the same for complex coefficients and the literal contragredient `E*` (complexification `cxFaceDual` and `dualIso` on `H²`, `toLiteral`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPoly.SmoothLocalDeRham

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

/-- **The seed class at the plane cusp `h⁻¹ P h`**: the de Rham class of the transported seed (holomorphic for `b = false`, antiholomorphic for `b = true`). -/
def cuspSeedClassAt (b : Bool) (h : SL(3, ℤ)) : groupCohomology.H2 (Rep.of (rhoAt N h n)) :=
  ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h) (rhoAt N h n)
    (if b then cuspSeedConjAt N n f h else cuspSeedAt N n f h)

/-- `resTo` to the plane cusp group is S6's de Rham class of the pullback of the series to the face of the cusp `h⁻¹ P h`. -/
theorem resTo_cuspFace (hn : 4 ≤ n) (h' : SL(3, ℤ)) (b : Bool) (h : SL(3, ℤ)) :
    resTo (gammaNPAt N h) (gammaNPAt_le N h) (gammaRho (gammaN N) n) (eisensteinAtClass_gammaN N n f h' b hn) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h) (rhoAt N h n)
        (cuspFaceForm N h (planeEisensteinAtComponents b (CuspData.ofSL h') (gammaN N) (leviGroup N) n f hn
          (leviInCusp_gammaN N h'))) :=
  (eisensteinAtClass_gammaN_cuspFace N n f hn h' b h).symm

/-- **`r_P ℰ_P = seed` at the plane cusp `h⁻¹ P h` of the series at that cusp**, both seeds (`3 ≤ N`, `4 ≤ n`). -/
theorem resTo_plane_seed (hn : 4 ≤ n) (hN : 3 ≤ N) (b : Bool) (h : SL(3, ℤ)) :
    resTo (gammaNPAt N h) (gammaNPAt_le N h) (gammaRho (gammaN N) n) (eisensteinAtClass_gammaN N n f h b hn) =
      cuspSeedClassAt N n f b h := by
  rw [resTo_cuspFace N n f hn h b h]
  cases b
  · exact constant_term_identity_at N n f hn h hN
  · exact constant_term_identity_at_conj N n f hn h hN

/-- **The dual series at the line cusp `h⁻¹ Q h`** for the seed of type `b`: `ȷ̃^*` of the series at the plane cusp `ȷ(h)`. -/
def dualSeriesAtClass_gammaN (hn : 4 ≤ n) (b : Bool) (h : SL(3, ℤ)) : groupCohomology.H2 (Rep.of (dualRhoN N n)) :=
  dualSeriesAtClass (gammaN N) (gammaN N) (jN N) (fun _ => rfl) (leviGroup N) n f hn b (CuspData.ofSL (jmath h))
    (leviInCusp_gammaN N (jmath h))

theorem dualSeriesAtClass_gammaN_eq (hn : 4 ≤ n) (b : Bool) (h : SL(3, ℤ)) :
    dualSeriesAtClass_gammaN N n f hn b h = jPull N n (eisensteinAtClass_gammaN N n f (jmath h) b hn) :=
  dualSeriesAtClass_eq (gammaN N) (gammaN N) (jN N) (fun _ => rfl) (leviGroup N) n f hn b (CuspData.ofSL (jmath h))
    (leviInCusp_gammaN N (jmath h))

/-- The dual seed class `η` at the line cusp `h⁻¹ Q h`: the `ȷ`-pullback of the seed class at the plane cusp `ȷ(h)`. -/
def dualSeedClassAt (b : Bool) (h : SL(3, ℤ)) :
    groupCohomology.H2 (Rep.of ((dualRhoN N n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))) :=
  pullQP N n h (cuspSeedClassAt N n f b (jmath h))

/-- **`r_Q ℰ_Q^∨ = η` at EVERY line cusp, for both seeds** (unconditional for `3 ≤ N`, `4 ≤ n`): transport of S6's
`constant_term_identity_at(_conj)` through `ȷ` (`dual_restrictions_transport`). -/
theorem dual_rQ_at (hn : 4 ≤ n) (hN : 3 ≤ N) (b : Bool) (h : SL(3, ℤ)) :
    resTo (gammaNQAt N h) (gammaNQAt_le_N N h) (dualRhoN N n) (dualSeriesAtClass_gammaN N n f hn b h) =
      dualSeedClassAt N n f b h := by
  rw [dualSeriesAtClass_gammaN_eq]
  refine ((dual_restrictions_transport (N := N) (n := n) (eisensteinAtClass_gammaN N n f (jmath h) b hn)).1 h).trans ?_
  unfold dualSeedClassAt
  rw [resTo_plane_seed N n f hn hN b (jmath h)]

/-- **`r_Q ℰ_Q^∨ = η` at every line cusp, for the literal contragredient `E*` and complex coefficients** (both seeds). -/
theorem dual_rQ_at_literal (hn : 4 ≤ n) (hN : 3 ≤ N) (b : Bool) (h : SL(3, ℤ)) :
    toLiteral (gammaNQAt N h) (gammaNQAt_le_N N h) n
      (cxFaceDual (gammaNQAt N h) (gammaNQAt_le_N N h) n
        (resTo (gammaNQAt N h) (gammaNQAt_le_N N h) (dualRhoN N n) (dualSeriesAtClass_gammaN N n f hn b h))) =
    toLiteral (gammaNQAt N h) (gammaNQAt_le_N N h) n
      (cxFaceDual (gammaNQAt N h) (gammaNQAt_le_N N h) n (dualSeedClassAt N n f b h)) := by
  rw [dual_rQ_at N n f hn hN b h]

end TernaryPeriodPolynomials.Argument.EisensteinDual
