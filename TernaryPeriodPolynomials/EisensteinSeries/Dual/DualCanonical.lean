module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.ComplexMirror
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.DualFlags
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NCanonical
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NSeedSurj

@[expose] public section


/-!
# Transport of the face data along `ȷ`, and the dual global class of a tuple of cusp forms

Formalized by Claude Sonnet 5.5.
Paper: "apply the preceding construction to `ȷ(Γ)` and pull back".  The faces of type `Q` of the dual construction are the `ȷ`-images of the
plane faces, with representatives `ȷ(planeFaceRepr x)`; those of type `P` are the `ȷ`-images of the line faces, with representatives `ȷ(LineFaces.rep i)`.

* `pullQP'`, `pullPQ'` (bijective): `ȷ^*` between the plane (resp. line) group at `r` (resp. `l`) and the line (resp. plane) group at `ȷ(r)` (resp. `ȷ(l)`);
  `resToC_dual_Q`, `resToC_dual_P`: transport of the restrictions.
* `dualSeedHolC_jmath`, `dualSeedConjC_jmath`, `dualCuspidalQ_jmath`, `dualClassC_jmath`: the dual seeds, `𝒞_Q(E^∨)` and dual series at the cusp `ȷ(r)` are the
  `ȷ`-pullbacks of the plane ones at `r`.
* `dualEJ`, `dualEJ_eq`: `ℰ^∨(u) = ∑_x ∑_b ℰ_Q^{∨,b}(u x b)` at the cusps `ȷ(planeFaceRepr x)`, equal to `ȷ^*` of the summed classical series `classCG u`.
-/

open scoped MatrixGroups DirectSum
open CategoryTheory
open scoped Classical
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.FormClassK

noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinDual

variable (N : ℕ) (n : ℕ)

section Transport

theorem jmath_Q_to_P' (r : SL(3, ℤ)) (s : gammaNQAt N (jmath r)) : jmath s.1 ∈ gammaNPAt N r := by
  have := jmath_Q_to_P (N := N) (jmath r) s
  rwa [jmath_jmath] at this

theorem jmath_P_to_Q' (l : SL(3, ℤ)) (s : gammaNPAt N (jmath l)) : jmath s.1 ∈ gammaNQAt N l := by
  have := jmath_P_to_Q (N := N) (jmath l) s
  rwa [jmath_jmath] at this

theorem jmath_mem_gammaNPAt_iff' (r A : SL(3, ℤ)) : jmath A ∈ gammaNPAt N r ↔ A ∈ gammaNQAt N (jmath r) := by
  have := jmath_mem_gammaNPAt_iff (N := N) (h := jmath r) (A := A)
  rwa [jmath_jmath] at this

theorem jmath_mem_gammaNQAt_iff' (l A : SL(3, ℤ)) : jmath A ∈ gammaNQAt N l ↔ A ∈ gammaNPAt N (jmath l) := by
  have := jmath_mem_gammaNQAt_iff (N := N) (h := jmath l) (A := A)
  rwa [jmath_jmath] at this

/-- `ȷ^*` from the plane group `Γ_{r⁻¹Pr}` (coefficients `E`) to the line group of the cusp `ȷ(r)` (coefficients `E^∨`). -/
def pullQP' (r : SL(3, ℤ)) :=
  facePullC (N := N) (gammaNQAt_le_N N (jmath r)) (gammaNPAt_le N r) (jmath_Q_to_P' N r) n

/-- `ȷ^*` from the line group `Γ_{l⁻¹Ql}` to the plane group of the cusp `ȷ(l)` (coefficients `E^∨`). -/
def pullPQ' (l : SL(3, ℤ)) :=
  facePullC (N := N) (gammaNPAt_le N (jmath l)) (gammaNQAt_le_N N l) (jmath_P_to_Q' N l) n

theorem pullQP'_bijective (r : SL(3, ℤ)) : Function.Bijective (pullQP' N n r) :=
  facePullC_bijective (gammaNQAt_le_N N (jmath r)) (gammaNPAt_le N r) (jmath_mem_gammaNPAt_iff' N r) n

theorem pullPQ'_bijective (l : SL(3, ℤ)) : Function.Bijective (pullPQ' N n l) :=
  facePullC_bijective (gammaNPAt_le N (jmath l)) (gammaNQAt_le_N N l) (jmath_mem_gammaNQAt_iff' N l) n

theorem resToC_dual_Q (r : SL(3, ℤ)) (c : groupCohomology.H2 (Rep.of (gammaRhoC (gammaN N) n))) :
    resToC N n (ρ := dualRhoC N n) (gammaNQAt N (jmath r)) (gammaNQAt_le_N N (jmath r)) (jPullC N n c) =
      pullQP' N n r (resToC N n (ρ := gammaRhoC (gammaN N) n) (gammaNPAt N r) (gammaNPAt_le N r) c) :=
  jPullC_res N n (gammaNQAt_le_N N (jmath r)) (gammaNPAt_le N r) (jmath_Q_to_P' N r) c

theorem resToC_dual_P (l : SL(3, ℤ)) (c : groupCohomology.H2 (Rep.of (gammaRhoC (gammaN N) n))) :
    resToC N n (ρ := dualRhoC N n) (gammaNPAt N (jmath l)) (gammaNPAt_le N (jmath l)) (jPullC N n c) =
      pullPQ' N n l (resToC N n (ρ := gammaRhoC (gammaN N) n) (gammaNQAt N l) (gammaNQAt_le_N N l) c) :=
  jPullC_res N n (gammaNPAt_le N (jmath l)) (gammaNQAt_le_N N l) (jmath_P_to_Q' N l) c

end Transport



section Main

variable [NeZero N]

theorem dualClassC_jmath (hn : 4 ≤ n) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (b : Bool) (r : SL(3, ℤ)) :
    dualClassC N n f hn b (jmath r) = jPullC N n (EisensteinClass.complexify (gammaN N) n
      (Statements.EisensteinClass.eisensteinAtClass_gammaN N n f r b hn)) := by
  unfold dualClassC
  rw [jmath_jmath]

theorem dualSeedHolC_aux (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (c r : SL(3, ℤ)) (e : jmath c = r)
    (hp : ∀ s : gammaNQAt N c, jmath s.1 ∈ gammaNPAt N r) :
    dualSeedHolC N n f c = facePullC (gammaNQAt_le_N N c) (gammaNPAt_le N r) hp n (faceSeedKerClass N r n f).1 := by
  subst e; rfl

theorem dualSeedConjC_aux (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (c r : SL(3, ℤ)) (e : jmath c = r)
    (hp : ∀ s : gammaNQAt N c, jmath s.1 ∈ gammaNPAt N r) :
    dualSeedConjC N n f c = facePullC (gammaNQAt_le_N N c) (gammaNPAt_le N r) hp n (faceSeedConjKerClass N r n f).1 := by
  subst e; rfl

/-- The dual holomorphic seed at the line cusp `ȷ(r)` is `ȷ^*` of the plane seed at `r`. -/
theorem dualSeedHolC_jmath (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (r : SL(3, ℤ)) :
    dualSeedHolC N n f (jmath r) = pullQP' N n r (faceSeedKerClass N r n f).1 :=
  dualSeedHolC_aux N n f (jmath r) r (jmath_jmath r) _

theorem dualSeedConjC_jmath (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (r : SL(3, ℤ)) :
    dualSeedConjC N n f (jmath r) = pullQP' N n r (faceSeedConjKerClass N r n f).1 :=
  dualSeedConjC_aux N n f (jmath r) r (jmath_jmath r) _

theorem dualCuspidalQ_aux (c r : SL(3, ℤ)) (e : jmath c = r) (hp : ∀ s : gammaNQAt N c, jmath s.1 ∈ gammaNPAt N r) :
    dualCuspidalQ N n c = Submodule.map (facePullC (gammaNQAt_le_N N c) (gammaNPAt_le N r) hp n)
      (faceCuspidalInH2 N r n) := by
  subst e; rfl

/-- `𝒞_Q(E^∨)` at the line cusp `ȷ(r)` is the `ȷ`-pullback of `𝒞_P(E)` at `r`. -/
theorem dualCuspidalQ_jmath (r : SL(3, ℤ)) :
    dualCuspidalQ N n (jmath r) = Submodule.map (pullQP' N n r) (faceCuspidalInH2 N r n) :=
  dualCuspidalQ_aux N n (jmath r) r (jmath_jmath r) _

/-- **The dual global class of a tuple of cusp forms**, indexed by the plane faces `x` of `Γ(N) = ȷ(Γ(N))`: the dual series at the line cusps
`ȷ(planeFaceRepr x)` (the representatives of the faces of type `Q` of the dual construction, i.e. `ȷ` applied to those of the plane construction). -/
def dualEJ (hn : 4 ≤ n) (u : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) : groupCohomology.H2 (Rep.of (dualRhoC N n)) :=
  ∑ x : PlaneFaces N, ∑ b : Bool, dualClassC N n (u x b) hn b (jmath (planeFaceRepr x))

theorem dualEJ_eq (hn : 4 ≤ n) (u : PlaneFaces N → Bool → CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) : dualEJ N n hn u = jPullC N n (classCG N n hn u) := by
  have hc : jPullC N n (classCG N n hn u) = jPullC N n (∑ x : PlaneFaces N, ∑ b : Bool,
      (EisensteinClass.complexify (gammaN N) n
        (Statements.EisensteinClass.eisensteinAtClass_gammaN N n (u x b) (planeFaceRepr x) b hn) :
          groupCohomology.H2 (Rep.of (gammaRhoC (gammaN N) n)))) := rfl
  rw [hc]
  unfold dualEJ
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun b _ => dualClassC_jmath N n hn _ b _

end Main

end TernaryPeriodPolynomials.Argument.EisensteinDual
