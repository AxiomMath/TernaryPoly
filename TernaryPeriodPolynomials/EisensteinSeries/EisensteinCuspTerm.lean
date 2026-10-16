module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.AntiHol
public import TernaryPeriodPolynomials.EisensteinSeries.Class.ComplexLinear

@[expose] public section


/-!
# Constant terms at every plane cusp of the same plane, antiholomorphic seed, complex scalars

Paper: "the same
letters for the rational conjugates".

## What is proved (`3 ≤ N`, `4 ≤ n`; every `h ∈ SL₃(ℤ)`)
* `constant_term_identity_at`: the class of the pullback to the boundary model `e(P)` (through the
  cusp map `i_h`, with the group `Γ_{h⁻¹Ph}` acting through `conjP N h`) of the HOLOMORPHIC series AT
  THE CUSP `h⁻¹ P h` equals the class of `cuspSeedAt N n f h`, the standard seed transported along
  `conjP N h` and the coefficient comparison `ρ(h⁻¹)`.
* `constant_term_identity_at_conj`: the same for the ANTIHOLOMORPHIC series and seed.
* `eisensteinClassC_cmul`, `eisensteinAtClassC_cmul`, `eisensteinAtClassC_add`: complex homogeneity
  (factor `cx b c`: complex-linear for the holomorphic seed, conjugate-linear for the antiholomorphic
  one; no hypothesis on `c`) and additivity of the complexified class at every cusp, in the cusp form.

## What is NOT proved here
The restriction to the face of a DIFFERENT cusp (off-diagonal terms) and the exact values
`resAtC N h n [E_{x,b}(f)]`; the identification of `cuspSeedAt` with the `faceSeedKerClass`.

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

section Cusp

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)
  (h : SL(3, ℤ))

/-- **Constant term of the holomorphic series at the cusp `h⁻¹ P h` along its own face is the
transported seed**. -/
theorem constant_term_identity_at (hN : 3 ≤ N) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
        (EisensteinClass.cuspFaceAction N h) (EisensteinClass.rhoAt N h n)
        (EisensteinClass.cuspFaceForm N h
          (planeEisensteinAtComponents false (CuspData.ofSL h) (gammaN N) (leviGroup N) n f hn
            (leviInCusp_gammaN N h))) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
        (EisensteinClass.cuspFaceAction N h) (EisensteinClass.rhoAt N h n)
        (EisensteinClass.cuspSeedAt N n f h) :=
  EisensteinClass.constant_term_identity_cusp N n f h hn hN

/-- **The same for the antiholomorphic series and seed.** -/
theorem constant_term_identity_at_conj (hN : 3 ≤ N) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
        (EisensteinClass.cuspFaceAction N h) (EisensteinClass.rhoAt N h n)
        (EisensteinClass.cuspFaceForm N h
          (planeEisensteinAtComponents true (CuspData.ofSL h) (gammaN N) (leviGroup N) n f hn
            (leviInCusp_gammaN N h))) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
        (EisensteinClass.cuspFaceAction N h) (EisensteinClass.rhoAt N h n)
        (EisensteinClass.cuspSeedConjAt N n f h) :=
  EisensteinClass.constant_term_identity_cusp_conj N n f hn h hN

end Cusp

section Scalars

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ)
  (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic]

/-- **Complex homogeneity of the complexified class of `𝓔_P(ω_f)` in the cusp form.** -/
theorem eisensteinClassC_cmul (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ) (c : ℂ)
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    eisensteinClassC Γ Λ n (c • f) hn hLevi = c • eisensteinClassC Γ Λ n f hn hLevi :=
  TernaryPeriodPolynomials.Argument.EisensteinClass.eisensteinClassC_cmul Γ n Λ hn hLevi c f

/-- **Series at any cusp and seed type: the class is `cx b`-linear in the cusp form.** -/
theorem eisensteinAtClassC_cmul (b : Bool) (D : CuspData) (hn : 4 ≤ n)
    (hLevi : LeviInCusp D Γ Λ) (c : ℂ) (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    eisensteinAtClassC b D Γ Λ n (c • f) hn hLevi =
      ConvergenceC4.cx b c • eisensteinAtClassC b D Γ Λ n f hn hLevi :=
  TernaryPeriodPolynomials.Argument.EisensteinClass.eisensteinAtClassC_cmul Γ n Λ b D hn hLevi c f

/-- **Additivity of the class of the series at any cusp and seed type in the cusp form.** -/
theorem eisensteinAtClassC_add (b : Bool) (D : CuspData) (hn : 4 ≤ n)
    (hLevi : LeviInCusp D Γ Λ) (f g : CuspForm Λ ((n + 3 : ℕ) : ℤ)) :
    eisensteinAtClassC b D Γ Λ n (f + g) hn hLevi =
      eisensteinAtClassC b D Γ Λ n f hn hLevi + eisensteinAtClassC b D Γ Λ n g hn hLevi :=
  TernaryPeriodPolynomials.Argument.EisensteinClass.eisensteinAtClassC_add Γ n Λ b D hn hLevi f g

end Scalars

end TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
