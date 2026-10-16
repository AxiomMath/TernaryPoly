module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Relations
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Transport
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Hecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreH2
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelThree
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH2

@[expose] public section


/-!
# The cusp decomposition of the cup pairing of `Γ₁(3)` and the Hecke cocycles

Basic ingredients of the proof that the cup pairing of `Γ₁(3)` is Hecke adjoint:

* `cupFormula_core_eq`: for the special elements `T`, `L⁻¹`, `(T L⁻¹)⁻¹` of `Γ₁(3)` the cup formula
  of a pair of crossed homomorphisms is the difference `loc_T - loc_L` of the local terms of any
  cup primitive at the cusp elements `T` and `L`, the local term at the cone point (of order 3)
  being zero;
* `H2_zero_HK`: the second cohomology of the stabilizer `H` with trivial complex coefficients
  vanishes (it embeds in `GL₂(ℤ)`), so cup primitives exist on `H`;
* `Data`: a pair of parabolic crossed homomorphisms of `Γ₁'(3)` normalized to vanish at `L`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets
open TernaryPeriodPolynomials.BoundaryDuality.AdjCore
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (rationalRho
  level_compat core_compat)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep coreRep)
open GeneralEisenstein
open TripleModel LinearDuality CocycleBridge EpsilonSplit

section CupFormula

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ core V} {ρ' : Representation ℂ core W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

/-- **The cup formula of `Γ₁(3)` is the difference of the local terms at the two cusps**:
`loc_T - loc_L` for any cup primitive. -/
theorem cupFormula_core_eq (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w) {X : core → V}
    {Y : core → W} {θ : core → ℂ} (hX : IsCocycle ρ X) (hY : IsCocycle ρ' Y)
    (hθ : IsCupPrimitive B ρ' X Y θ) {v : V × V × V} (hv : IsPrimitive ρ coreT coreL⁻¹ X v) :
    cupFormula B ρ' coreT coreL⁻¹ X Y v = localTerm B θ Y coreT v.1 - localTerm B θ Y coreL v.2.1 := by
  rw [cupFormula_eq_localTerm hX hθ]
  have h3 : localTerm B θ Y (coreT * coreL⁻¹)⁻¹ v.2.2 = 0 :=
    localTerm_eq_zero_of_pow_eq_one hinv hX hY hθ hv.2.2 (by norm_num : 0 < 3)
      (by rw [inv_pow, core_elliptic_cube, inv_one])
  have h2 := localTerm_inv hinv hX hY hθ (primitive_of_inv hX hv.2.1)
  rw [h3, h2]
  ring

end CupFormula

section Vanishing

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- **The second cohomology of the stabilizer vanishes** (it embeds in `GL₂(ℤ)`). -/
theorem H2_zero_HK : ∀ x : groupCohomology.H2 (Rep.trivial ℂ (HK p hp3) ℂ), x = 0 := by
  intro x
  refine Spectral.ModularH2.H2_zero_of_injective_binary
    ((binaryArithmeticLevel.subtype.comp (core.subtype.comp (HK p hp3).subtype)).prod 1) ?_ _ x
  intro a b hab
  exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg Prod.fst hab)))

end Vanishing

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
