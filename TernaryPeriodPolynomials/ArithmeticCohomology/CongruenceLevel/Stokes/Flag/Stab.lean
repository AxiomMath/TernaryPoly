module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Vanish
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.NeatSingular

@[expose] public section


/-!
# The complete flags of `Γ(6)`: finitely many orbits, and the stabilizers are the flag groups

Formalized by Claude Sonnet 5.5.

* `flagOrbits_finite`, `flagOrbitsFintype`: the set `labelOrbits Γ6 Flag` of `Γ(6)`-orbits of complete flags is finite (every orbit is that of some `flagOf g`, and `flagOf (g γ)` is in the orbit of `flagOf g`
  for `γ ∈ Γ(6)`, `SL₃(ℤ) ⧸ Γ(6)` being finite);
* `flagEmb_injective`, `flagEmb_range`, `flagStabEquiv`: the flag group `Γ(6) ∩ g⁻¹Bg` is the stabilizer of the flag `flagOf g`.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

instance flagOrbits_finite : Finite (labelOrbits Γ6 Flag) := by
  have : (gammaN 6).FiniteIndex :=
    TernaryPeriodPolynomials.Argument.GeneralCoercivity.finiteIndex_gammaN 6
  have : Finite (SL(3, ℤ) ⧸ gammaN 6) := Subgroup.finite_quotient_of_finiteIndex
  let f : SL(3, ℤ) ⧸ gammaN 6 → labelOrbits Γ6 Flag :=
    Quotient.lift (fun g => (Quotient.mk'' (flagOf g) : labelOrbits Γ6 Flag)) (by
      intro a b hab
      have hp : a⁻¹ * b ∈ gammaN 6 := (QuotientGroup.leftRel_apply).mp hab
      apply Quotient.sound'
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨gammaSixEquiv ⟨a⁻¹ * b, hp⟩, ?_⟩
      rw [smul_flagOf]
      congr 1
      group)
  have hf : Function.Surjective f := by
    intro x
    induction x using Quotient.inductionOn' with
    | h F =>
      obtain ⟨g, rfl⟩ := exists_flagOf F
      exact ⟨QuotientGroup.mk g, rfl⟩
  exact Finite.of_surjective f hf

noncomputable instance flagOrbitsFintype : Fintype (labelOrbits Γ6 Flag) :=
  Fintype.ofFinite _

theorem flagEmb_injective (g : SL(3, ℤ)) : Function.Injective (flagEmb g) :=
  gammaSixEquiv.injective.comp (Subgroup.inclusion_injective _)

theorem flagEmb_range (g : SL(3, ℤ)) : (flagEmb g).range = MulAction.stabilizer Γ6 (flagOf g) := by
  ext γ
  constructor
  · rintro ⟨p, rfl⟩
    exact flagEmb_mem g p
  · intro hγ
    obtain ⟨s, hs⟩ := (flagAlpha_bijective g).2 ⟨γ, hγ⟩
    exact ⟨s, congrArg Subtype.val hs⟩

/-- **The stabilizer of the complete flag `flagOf g` in `Γ(6)` is the flag group `Γ(6) ∩ g⁻¹ B g`.** -/
def flagStabEquiv (g : SL(3, ℤ)) : ↥(gammaNBAt 6 g) ≃* ↥(MulAction.stabilizer Γ6 (flagOf g)) :=
  MulEquiv.ofBijective (flagAlpha g) (flagAlpha_bijective g)

theorem flagStabEquiv_apply (g : SL(3, ℤ)) (p : gammaNBAt 6 g) :
    ((flagStabEquiv g p : MulAction.stabilizer Γ6 (flagOf g)) : Γ6) = flagEmb g p := rfl

end TernaryPeriodPolynomials.Argument.GammaNStokes
