module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelDescent.RestrictEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelDescent.LineData
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.FibreIndex
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Terms
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Final

@[expose] public section


/-!
# Restriction of the canonical pairing from a line face of `Γ(N)` to the line faces of `Γ(M)`

Formalized by Claude Sonnet 5.5.

For `N ∣ M` and a frame `h`, the canonical pairing at the line cusp `h⁻¹Qh` of the restrictions to `Γ(M)` of global classes of `Γ(N)` is
`(M/N)² [Γ(N):Γ(M)] = [Γ_h(N) : Γ_h(M)]` times their pairing at level `N`.
-/

open scoped MatrixGroups
noncomputable section

namespace TernaryPeriodPolynomials.Argument.LevelDescent

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
open TernaryPeriodPolynomials.Argument.RadicalInduction
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open scoped Classical

section Classes

variable {N M : ℕ} (n : ℕ)

/-- Restriction of a class of `H²(Γ(N), E_n^*)` to level `M`. -/
def resLevelDual (hNM : N ∣ M) :
    groupCohomology.H2 (gammaNRepAllDual N n) →ₗ[ℂ] groupCohomology.H2 (gammaNRepAllDual M n) :=
  twoCohomologyRestriction (Subgroup.inclusion (gammaN_mono hNM)) (gammaNRepAllDual N n)

theorem zeroFlags_resLevelDual (hNM : N ∣ M) (c' : groupCohomology.H2 (gammaNRepAllDual N n))
    (hz' : ZeroFlagsRep (gammaNRepAll N n).ρ.dual c') : ZeroFlagsRep (gammaNRepAll M n).ρ.dual (resLevelDual n hNM c') := by
  intro g
  exact res_res_eq_zero (Subgroup.inclusion (gammaN_mono hNM)) (Subgroup.inclusion (gammaNBAt_le_gammaN M g))
    (Subgroup.inclusion (gammaNBAt_le_gammaN N g)) (Subgroup.inclusion (gammaNBAt_mono hNM g)) (by ext; rfl)
    (gammaNRepAllDual N n) c' (hz' g)

end Classes

section Line

variable {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (h : SL(3, ℤ))

/-- The inclusion of the line group of level `M` in that of level `N`. -/
def lineIota : gammaNQAt M h →* gammaNQAt N h := Subgroup.inclusion (gammaNQAt_mono hNM h)

omit [NeZero N] [NeZero M] in
theorem radEltQ_scale {k : ℕ} (hk : M = N * k) (r : RadicalLattice) : radEltQ M r = radEltQ N (r ^ k) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [radEltQ, hk, mul_assoc]

theorem lineIota_inl (r : RadicalLattice) :
    lineIota hNM h ((lineFaceExt M h).inl r) = (lineFaceExt N h).inl (radScale (M / N) r) := by
  apply Subtype.ext
  change h⁻¹ * radEltQ M r * h = h⁻¹ * radEltQ N (r ^ (M / N)) * h
  rw [radEltQ_scale (k := M / N) (Nat.mul_div_cancel' hNM).symm]

theorem lineIota_split (l : Gamma M) :
    lineIota hNM h ((lineFaceSplitting M h) l) =
      (lineFaceSplitting N h) (Subgroup.inclusion (Gamma_le_of_dvd hNM) l) := rfl

end Line

end TernaryPeriodPolynomials.Argument.LevelDescent
