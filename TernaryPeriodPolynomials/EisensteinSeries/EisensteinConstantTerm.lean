module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.ConstantTerm
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.Face
public import TernaryPeriodPolynomials.EisensteinSeries.Class.ZeroClass

@[expose] public section


/-!
# Constant terms of the literal Eisenstein class (Appendix C.4): the reduction

Paper: "the identity
constant term represents exactly `ξ`".

## What is proved
* `resP_eisensteinClass_eq`: unfolding over `Γ_P \\ Γ`, the restriction to `Γ_P = Γ(N) ∩ P(ℤ)` of
  `eisensteinClass_gammaN` is `cuspSeedClass` (the identity coset, scalar `1`) plus the de Rham class
  of `restFaceForm`, the invariant closed form on `e(P)` whose coordinates are the sums over the
  non-identity cosets (`restFaceForm_basis`).
* `resP_eisensteinClass_iff`: the constant-term identity `r_P [𝓔_P(ω_h)] = [seed of f]` holds
  if and only if `ConstantTermVanishing N n f hn`.
* `constantTermVanishing_of_equivariant_primitive`: `ConstantTermVanishing` follows from an
  equivariant primitive of `restFaceForm`.
* `eisensteinClass_gammaN_cuspFace`, `eisensteinAtClass_gammaN_cuspFace`: for EVERY plane cusp
  `h⁻¹ P h` of `Γ(N)`, the restriction to `Γ_{h⁻¹Ph}` of the class of the series (at the standard
  cusp, resp. at any cusp datum and seed type) is the de Rham class of its pullback to the
  boundary model of that cusp (`cuspFaceForm`, with coordinates `toPoly_cuspFaceForm_basis`).

## What is NOT proved
`ConstantTermVanishing` itself (zero modes of the `s₂₃` coset terms by cuspidality, with Kasuya's
comparison for the nilmanifold average), and the identification of the same-plane cosets at other
cusps with seeds of the translated forms.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane MatrixGroups ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.EisensteinClass

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
open TernaryPoly.SmoothLocalDeRham

section GammaN

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)

/-- **Constant term of the literal class, reduction**. -/
theorem constant_term_reduction :
    EisensteinClass.resP N n (eisensteinClass_gammaN N n f hn) =
      cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) +
        ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
          (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n)
          (EisensteinClass.restFaceForm N n f hn) :=
  EisensteinClass.resP_eisensteinClass_eq N n f hn

/-- **The constant-term identity is equivalent to the vanishing of the non-identity part.** -/
theorem constant_term_iff :
    EisensteinClass.resP N n (eisensteinClass_gammaN N n f hn) =
      cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) ↔
    EisensteinClass.ConstantTermVanishing N n f hn :=
  EisensteinClass.resP_eisensteinClass_iff N n f hn

/-- **A sufficient condition**: an equivariant primitive of the non-identity part. -/
theorem constantTermVanishing_of_equivariant_primitive
    (pr : Form (F := Coef n) faceSet 1)
    (hpr : d isOpen_faceSet 1 pr = (EisensteinClass.restFaceForm N n f hn : Form (F := Coef n) faceSet 2))
    (hinv : ∀ g, ZigZag.pullForm isOpen_faceSet (gammaNPlaneData N).action g 1 pr =
      ZigZag.twForm (ZigZag.repCLM ((gammaNPlaneData N).rhoR n) g) 1 pr) :
    EisensteinClass.ConstantTermVanishing N n f hn :=
  EisensteinClass.deRhamClass_eq_zero_of_equivariant_primitive isOpen_faceSet convex_faceSet
    faceSet_nonempty _ _ _ pr hpr hinv

/-- **Restriction to the face of an arbitrary plane cusp** `h⁻¹ P h` of `Γ(N)`: the group restriction to `Γ_{h⁻¹Ph}` of `eisensteinClass_gammaN` is the de Rham class of
the pullback of the series to the boundary model of the cusp. -/
theorem eisensteinClass_gammaN_cuspFace (h : SL(3, ℤ)) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
        (EisensteinClass.cuspFaceAction N h) (EisensteinClass.rhoAt N h n)
        (EisensteinClass.cuspFaceForm N h
          (planeEisensteinComponents (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N))) =
      (groupCohomology.map (EisensteinClass.inclAt N h)
          (resMor (EisensteinClass.inclAt N h) (EisensteinClass.rhoAt N h n)
            (gammaRho (gammaN N) n) (fun _ => rfl)) 2).hom
        (eisensteinClass_gammaN N n f hn) :=
  EisensteinClass.cuspFaceForm_class N h _

/-- The same for the series at an arbitrary plane cusp `h'` and seed type `b`. -/
theorem eisensteinAtClass_gammaN_cuspFace (h' : SL(3, ℤ)) (b : Bool) (h : SL(3, ℤ)) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
        (EisensteinClass.cuspFaceAction N h) (EisensteinClass.rhoAt N h n)
        (EisensteinClass.cuspFaceForm N h
          (planeEisensteinAtComponents b (CuspData.ofSL h') (gammaN N) (leviGroup N) n f hn
            (leviInCusp_gammaN N h'))) =
      (groupCohomology.map (EisensteinClass.inclAt N h)
          (resMor (EisensteinClass.inclAt N h) (EisensteinClass.rhoAt N h n)
            (gammaRho (gammaN N) n) (fun _ => rfl)) 2).hom
        (eisensteinAtClass_gammaN N n f h' b hn) :=
  EisensteinClass.cuspFaceForm_class N h _

end GammaN

end TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
