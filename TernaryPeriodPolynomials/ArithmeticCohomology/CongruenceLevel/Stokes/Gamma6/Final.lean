module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Vanish
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.PropC5GammaN

@[expose] public section


/-!
# Lemma `ar:lem:stokes` at level `Γ(6)`: the Stokes relation for global classes with zero flag restrictions

Formalized by Claude Sonnet 5.5.

For classes `c ∈ H²(Γ(6), E)`, `c' ∈ H²(Γ(6), E^*)` (`E^*` the contragredient) with zero restriction to every flag group `Γ(6) ∩ g⁻¹Bg`, the sum over the line faces `Γ(6) ∩ h⁻¹Qh`
of the face pairings of the restrictions of `c`, `c'`, plus the sum over the plane faces `Γ(6) ∩ h⁻¹Ph`, vanishes (`gamma6_stokes_of_zeroFlags`).  The face pairings are the
orbit pairings of the cone model (`lineFacePairM`, `planeFacePairM`), i.e. the pairings of the cone lifts of the face classes.  For `E = E_n` this is
`gamma6_stokes_En`, with `ZeroFlags 6 n c` the hypothesis of `PropC5GammaN`.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.SeedC3

section Final

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V)

/-- **Lemma `ar:lem:stokes` at level `Γ(6)`.** -/
theorem gamma6_stokes_of_zeroFlags
    (c : groupCohomology.H2 (Rep.of ρ)) (c' : groupCohomology.H2 (Rep.of ρ.dual))
    (hz : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp))
      (Rep.of ρ) c = 0)
    (hz' : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp))
      (Rep.of ρ.dual) c' = 0) :
    ∑ i : LineFaces 6, lineFacePairM ρ i
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ) c)
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual) c') +
      ∑ i : PlaneFaces 6, planeFacePairM ρ i
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ) c)
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) (Rep.of ρ.dual) c') = 0 := by
  obtain ⟨X, h1, h2⟩ := exists_flag_vanishing_of_res (rep6 ρ) (toGamma6 ρ c) (res_stab_flag_zero ρ c hz)
  obtain ⟨X', h1', h2'⟩ := exists_flag_vanishing_of_res (rep6 ρ).dual (toGamma6Dual ρ c')
    (res_stab_flag_zero_dual ρ c' hz')
  exact gamma6_stokes_mathlib ρ c c' ⟨X, X', h1, h1', h2, h2'⟩

end Final


section En

variable (n : ℕ)

/-- The coefficient representation `E_n` of `Γ(6)`. -/
def rhoEn : Representation ℂ (gammaN 6) (HomogeneousPoly n) := (ambRep n).comp (gammaN 6).subtype

/-- The contragredient `E_n^*` of `E_n` over `Γ(N)` (the literal linear dual, with the contragredient action). -/
def gammaNRepAllDual (N : ℕ) (n : ℕ) : Rep ℂ (gammaN N) := Rep.of ((gammaNRepAll N n).ρ.dual)

/-- **Lemma `ar:lem:stokes` at level `Γ(6)` for `E_n` and its dual**, with the notation `rLine`, `rPlane`, `ZeroFlags` of `PropC5GammaN`. -/
theorem gamma6_stokes_En
    (c : groupCohomology.H2 (gammaNRepAll 6 n)) (c' : groupCohomology.H2 (gammaNRepAllDual 6 n))
    (hz : ZeroFlags 6 n c)
    (hz' : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp))
      (gammaNRepAllDual 6 n) c' = 0) :
    ∑ i : LineFaces 6, lineFacePairM (rhoEn n) i (rLine 6 n i.rep c)
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp))
          (gammaNRepAllDual 6 n) c') +
      ∑ i : PlaneFaces 6, planeFacePairM (rhoEn n) i (rPlane 6 n (planeFaceRepr i) c)
        (twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp))
          (gammaNRepAllDual 6 n) c') = 0 :=
  gamma6_stokes_of_zeroFlags (rhoEn n) c c' hz hz'

end En

end TernaryPeriodPolynomials.Argument.GammaNStokes
