module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.FlagReduction
public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinConstantTerm
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.Face
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Complexify
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.LocallyInner

@[expose] public section


/-!
# Flag restrictions at every plane cusp `h⁻¹ P h`: complexification of the cusp-face classes

Formalized by Claude Sonnet 5.5.

the face classes at the plane cusp `h⁻¹Ph` (`cuspFaceForm`, `eisensteinClass_gammaN_cuspFace`) have values in the REAL
coefficient representation `rhoAt N h n`, whereas the mixed cuspidal / locally inner groups
(`faceCuspidalInH2`, `faceLocallyInner`, `faceFlagStab`) live in the complex representation `faceRep N h n`.  Both are the
restriction of the coefficient representation to the plane group `Γ_{h⁻¹Ph} = gammaNPAt N h`, and
`rhoAt N h n = gammaRho (gammaNPAt N h) n`, `faceRep N h n = gammaRep (gammaNPAt N h) n` hold by `rfl`.  Hence the generic
complexification `complexify (gammaNPAt N h) n` (identity on cocycles) is the missing bridge `complexifyAt`.

* `flag_mem_locallyInner_iff`: the complexified class vanishes on the radical and on the stabilizer of every complete flag over
  the plane `h⁻¹Ph` iff it is locally inner;
* `flag_vanishing_at_cusp`: if the complexified restriction of a class to `Γ_{h⁻¹Ph}` is mixed cuspidal, it vanishes at every
  flag over the plane (`r_B = 0`);
* `flag_restriction_eq_rest_at`: if the restriction splits as (mixed cuspidal part) + (rest), the flag restriction is that of the
  rest, at every flag over the plane `h⁻¹Ph`;
* `rB_eq_flag_of_cuspFace`: the flag restriction of the series is the flag restriction of the complexified de Rham class of its
  pullback to the boundary model of the cusp.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers

section Cusp

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (n : ℕ)

/-- **Complexification of the classes of the plane group of the cusp `h⁻¹ P h`** (identity on cocycles). -/
def complexifyAt : groupCohomology.H2 (Rep.of (rhoAt N h n)) →ₗ[ℝ] groupCohomology.H2 (faceRep N h n) :=
  complexify (gammaNPAt N h) n

/-- A complexified class of the plane group is locally inner iff it vanishes on the radical and on the stabilizer of every
complete flag over the plane. -/
theorem flag_mem_locallyInner_iff (y : groupCohomology.H2 (Rep.of (rhoAt N h n))) :
    complexifyAt N h n y ∈ faceLocallyInner N h n ↔
      twoCohomologyRestriction (faceExt N h).inl (faceRep N h n) (complexifyAt N h n y) = 0 ∧
        ∀ F : GL (Fin 2) ℚ, twoCohomologyRestriction (faceFlagStab N h F).subtype (faceRep N h n)
          (complexifyAt N h n y) = 0 := by
  unfold faceLocallyInner
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

/-- **`r_B = 0` at every flag over the plane `h⁻¹Ph`, if the restriction to the plane group is mixed cuspidal.** -/
theorem flag_vanishing_at_cusp (y : groupCohomology.H2 (Rep.of (rhoAt N h n)))
    (hy : complexifyAt N h n y ∈ faceCuspidalInH2 N h n) (F : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (faceFlagStab N h F).subtype (faceRep N h n) (complexifyAt N h n y) = 0 := by
  rw [faceCuspidalInH2_eq_locallyInner] at hy
  exact ((flag_mem_locallyInner_iff N h n y).mp hy).2 F

/-- **Splitting the plane restriction into a mixed cuspidal part and a rest**: the flag restriction is that of the rest, at every
flag over the plane `h⁻¹Ph`. -/
theorem flag_restriction_eq_rest_at (y s r : groupCohomology.H2 (Rep.of (rhoAt N h n))) (hdec : y = s + r)
    (hs : complexifyAt N h n s ∈ faceCuspidalInH2 N h n) (F : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (faceFlagStab N h F).subtype (faceRep N h n) (complexifyAt N h n y) =
      twoCohomologyRestriction (faceFlagStab N h F).subtype (faceRep N h n) (complexifyAt N h n r) := by
  rw [hdec, map_add, map_add, flag_vanishing_at_cusp N h n s hs F, zero_add]

/-- If the rest vanishes, so does the flag restriction. -/
theorem flag_vanishing_of_decomposition (y s : groupCohomology.H2 (Rep.of (rhoAt N h n)))
    (hdec : y = s) (hs : complexifyAt N h n s ∈ faceCuspidalInH2 N h n) (F : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (faceFlagStab N h F).subtype (faceRep N h n) (complexifyAt N h n y) = 0 := by
  subst hdec
  exact flag_vanishing_at_cusp N h n y hs F

end Cusp

section Series

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPoly.SmoothLocalDeRham
open MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)

/-- **The flag restriction of the series at the flags over the cusp `h⁻¹ P h`** is the flag restriction of the complexified de Rham
class of the pullback of the series to the boundary model of that cusp (`eisensteinClass_gammaN_cuspFace`). -/
theorem rB_eq_flag_of_cuspFace (F : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (faceFlagStab N h F).subtype (faceRep N h n)
      (complexifyAt N h n ((groupCohomology.map (inclAt N h)
          (resMor (inclAt N h) (rhoAt N h n) (gammaRho (gammaN N) n) (fun _ => rfl)) 2).hom
        (eisensteinClass_gammaN N n f hn))) =
    twoCohomologyRestriction (faceFlagStab N h F).subtype (faceRep N h n)
      (complexifyAt N h n (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
        (cuspFaceAction N h) (rhoAt N h n)
        (cuspFaceForm N h
          (planeEisensteinComponents (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N))))) := by
  rw [eisensteinClass_gammaN_cuspFace N n f hn h]

end Series

end TernaryPeriodPolynomials.Argument.EisensteinClass
