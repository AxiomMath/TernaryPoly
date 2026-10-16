module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.ConstantTerm
public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinConstantTerm
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.MixedCuspidal
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.LocallyInner

@[expose] public section


/-!
# The flag constant term `r_B 𝓔_P(ξ) = 0` (B row of the unfolding table): reduction to the plane

Formalized by Claude Sonnet 5.5.

**Mathematical point.**  A complete flag lies over a unique plane, and the stabilizer of the flag (in `Γ(N)`) lies in the
stabilizer `Γ_P` of that plane (here `Γ(N) ∩ P(ℤ)` for the standard plane; its elements with Levi block fixing a rational cusp
`F · ∞` of the binary Levi, `LocallyInner.incl (gammaNExt N) (leviCuspStab Γ(N) F)`).  Hence the restriction `r_B` of any class to a
flag is the restriction of `r_P` of the class to the flag stabilizer (group-cohomology functoriality), and no averaging over the
Heisenberg radical is needed once the plane constant term is known: the paper's B row only has to explain why the flag restriction
of `r_P 𝓔_P(ξ) = ξ + (non-identity part)` vanishes, and

* the identity-coset part is the seed, a mixed cuspidal class (`gammaNSeedSpan_le_cuspidalInH2`), which vanishes on every flag
  stabilizer (`gammaNCuspidalInH2_flag_vanish`, from the Hochschild-Serre characterization
  `LocallyInner.edge_mem_cuspidalFamily_iff` and `H²` vanishing for the level group): this is the row `I` of the table (the binary root
  average is zero by cuspidality) — **proved** (`seed_flag_vanish`);
* the non-identity part is the class of `restFaceForm`: `flag_restriction_eq_rest` (**unconditional**): the flag restriction of
  `𝓔_P(ω_f)` equals the flag restriction of `[restFaceForm]`; and `flag_vanishing_of_constantTerm`: if
  `ConstantTermVanishing N n f hn` (the plane constant term, the obligation (b)) holds, every flag restriction vanishes.

What is NOT proved: `ConstantTermVanishing` itself, and the flags over the other plane cusps `h⁻¹ P h` (which need the
corresponding decomposition of `r_{h⁻¹Ph} 𝓔` into seeds and a non-identity part, the O2).  The coefficient system here is the
complexification (`complexifyG`) of the real class of the de Rham series.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPoly.SmoothLocalDeRham

section Flag

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **The mixed cuspidal classes of the standard plane group vanish on every flag stabilizer.** -/
theorem gammaNCuspidalInH2_flag_vanish (y : groupCohomology.H2 (gammaNRep N n))
    (hy : y ∈ gammaNCuspidalInH2 N n) (F : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (LocallyInner.incl (gammaNExt N)
      (leviCuspStab (CongruenceSubgroup.Gamma N) F)) (gammaNRep N n) y = 0 := by
  have hB : ∀ (F : GL (Fin 2) ℚ) (V : Rep ℂ ↥(leviCuspStab (CongruenceSubgroup.Gamma N) F))
      (x : groupCohomology.H2 V), x = 0 := fun F V x =>
    LocallyInner.h2_zero_subgroup
      (fun A x => H2_vanish_level (CongruenceSubgroup.Gamma N) A x) _ V x
  obtain ⟨x, hx, rfl⟩ := hy
  have := (LocallyInner.edge_mem_cuspidalFamily_iff (gammaNSplitting N) (gammaNRep N n)
    (leviCuspStab (CongruenceSubgroup.Gamma N)) hB x.1 x.2).mp hx
  exact this F

variable (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)

/-- The complexified seed class of `f` vanishes on every flag stabilizer of the standard plane group. -/
theorem seed_flag_vanish (F : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (LocallyInner.incl (gammaNExt N)
      (leviCuspStab (CongruenceSubgroup.Gamma N) F)) (gammaNRep N n)
      (complexifyG N n (cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f))) = 0 :=
  gammaNCuspidalInH2_flag_vanish N n _
    (gammaNSeedSpan_le_cuspidalInH2 N n (Submodule.subset_span (Or.inl ⟨f, rfl⟩))) F

/-- **The flag restriction of the series is the flag restriction of its non-identity part** (unconditional): the restriction to
the stabilizer of any complete flag over the standard plane of the (complexified) class of `𝓔_P(ω_f)` equals that of the class of
`restFaceForm`.  The identity coset (the row `I` of the unfolding table) contributes nothing at a flag, since the
seed is mixed cuspidal. -/
theorem flag_restriction_eq_rest (F : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (LocallyInner.incl (gammaNExt N)
      (leviCuspStab (CongruenceSubgroup.Gamma N) F)) (gammaNRep N n)
      (complexifyG N n (resP N n (eisensteinClass_gammaN N n f hn))) =
    twoCohomologyRestriction (LocallyInner.incl (gammaNExt N)
      (leviCuspStab (CongruenceSubgroup.Gamma N) F)) (gammaNRep N n)
      (complexifyG N n (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
          (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n) (restFaceForm N n f hn))) := by
  rw [resP_eisensteinClass_eq, map_add, map_add, seed_flag_vanish N n f F, zero_add]

/-- **`r_B 𝓔_P(ω_f) = 0` at every flag over the standard plane, given the plane constant term.** -/
theorem flag_vanishing_of_constantTerm (hO : ConstantTermVanishing N n f hn) (F : GL (Fin 2) ℚ) :
    twoCohomologyRestriction (LocallyInner.incl (gammaNExt N)
      (leviCuspStab (CongruenceSubgroup.Gamma N) F)) (gammaNRep N n)
      (complexifyG N n (resP N n (eisensteinClass_gammaN N n f hn))) = 0 := by
  rw [flag_restriction_eq_rest N n f hn F]
  have : ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
          (gammaNPlaneData N).action ((gammaNPlaneData N).rhoR n) (restFaceForm N n f hn) = 0 := hO
  rw [this, map_zero, map_zero]

end Flag

end TernaryPeriodPolynomials.Argument.EisensteinClass
