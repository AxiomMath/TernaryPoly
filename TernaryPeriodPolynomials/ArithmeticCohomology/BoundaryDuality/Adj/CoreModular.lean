module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreLocal
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelOne

@[expose] public section


/-!
# The cup formula of `SL₂(ℤ)` is the local term at the cusp

For `SL₂(ℤ)` with the special elements `a = S`, `g₂ = T⁻¹`, `g₃ = (S T⁻¹)⁻¹` the elements `S` and
`g₃` have finite order (four and three), so their local terms vanish for every cup primitive, and
the cup formula of the triple model is minus the local term at `T`.  When the second cocycle
vanishes at `T` this is `-θ T` (`cupFormula_eq_neg_theta`): the cup pairing of a parabolic class is
read off from any primitive of the scalar cup product at the generator of the cusp.

A crossed homomorphism vanishing at `t` vanishes on all powers of `t`
(`isCocycle_zpow_eq_zero`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjCore

open TripleModel LinearDuality CocycleBridge EpsilonSplit
open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- A crossed homomorphism vanishing at `t` vanishes at every power of `t`. -/
theorem isCocycle_zpow_eq_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {x : G → V} (hx : IsCocycle ρ x) {t : G} (ht : x t = 0) (n : ℤ) :
    x (t ^ n) = 0 := by
  let H : Subgroup G :=
    { carrier := {g | x g = 0}
      mul_mem' := fun {a b} ha hb => by
        change x (a * b) = 0
        change x a = 0 at ha
        change x b = 0 at hb
        rw [hx a b, ha, hb, map_zero, add_zero]
      one_mem' := hx.map_one
      inv_mem' := fun {a} ha => by
        change x a⁻¹ = 0
        change x a = 0 at ha
        rw [isCocycle_map_inv hx a, ha, map_zero, neg_zero] }
  have htH : t ∈ H := ht
  exact H.zpow_mem htH n

section Modular

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) V}
  {ρ' : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}
  {X : Matrix.SpecialLinearGroup (Fin 2) ℤ → V} {Y : Matrix.SpecialLinearGroup (Fin 2) ℤ → W}
  {θ : Matrix.SpecialLinearGroup (Fin 2) ℤ → ℂ}

/-- `(S T⁻¹)⁻¹` has order three. -/
theorem modularCone_inv_cube :
    ((ModularGroup.S * ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹) ^ 3 = 1 := by
  have hcube : (ModularGroup.S * ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) ^ 3 = 1 :=
    ParabolicDuality.LevelOne.modularCone_cube
  rw [inv_pow, hcube, inv_one]

/-- **The cup formula of `SL₂(ℤ)` is minus the local term at the cusp generator `T`.** -/
theorem cupFormula_eq_neg_localTerm (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    (hX : IsCocycle ρ X) (hY : IsCocycle ρ' Y) (hθ : IsCupPrimitive B ρ' X Y θ)
    {v : V × V × V} (hv : IsPrimitive ρ ModularGroup.S ModularGroup.T⁻¹ X v) :
    cupFormula B ρ' ModularGroup.S ModularGroup.T⁻¹ X Y v =
      -localTerm B θ Y ModularGroup.T v.2.1 := by
  have h1 := localTerm_eq_zero_of_pow_eq_one hinv hX hY hθ hv.1 (by norm_num : 0 < 4)
    modularOrderFour
  have h3 := localTerm_eq_zero_of_pow_eq_one hinv hX hY hθ hv.2.2 (by norm_num : 0 < 3)
    modularCone_inv_cube
  have h2 := localTerm_inv hinv hX hY hθ (primitive_of_inv hX hv.2.1)
  rw [cupFormula_eq_localTerm hX hθ, h1, h3, h2]
  ring

/-- **The cup formula at a second cocycle vanishing at `T`** is `-θ T` for every cup
primitive `θ`. -/
theorem cupFormula_eq_neg_theta (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    (hX : IsCocycle ρ X) (hY : IsCocycle ρ' Y) (hθ : IsCupPrimitive B ρ' X Y θ)
    {v : V × V × V} (hv : IsPrimitive ρ ModularGroup.S ModularGroup.T⁻¹ X v)
    (hYT : Y ModularGroup.T = 0) :
    cupFormula B ρ' ModularGroup.S ModularGroup.T⁻¹ X Y v = -θ ModularGroup.T := by
  rw [cupFormula_eq_neg_localTerm hinv hX hY hθ hv, localTerm_def, hYT, map_zero, sub_zero]

/-- The cup formula against a second cocycle whose value at `T` pairs to zero with the cusp
primitive of the first: `-θ T`. -/
theorem cupFormula_eq_neg_theta_of_pair (hinv : ∀ g v w, B (ρ g v) (ρ' g w) = B v w)
    (hX : IsCocycle ρ X) (hY : IsCocycle ρ' Y) (hθ : IsCupPrimitive B ρ' X Y θ)
    {v : V × V × V} (hv : IsPrimitive ρ ModularGroup.S ModularGroup.T⁻¹ X v)
    (hpair : B v.2.1 (Y ModularGroup.T) = 0) :
    cupFormula B ρ' ModularGroup.S ModularGroup.T⁻¹ X Y v = -θ ModularGroup.T := by
  rw [cupFormula_eq_neg_localTerm hinv hX hY hθ hv, localTerm_def, hpair, sub_zero]

end Modular

end TernaryPeriodPolynomials.BoundaryDuality.AdjCore
