module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.GammaNTransfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.LineFaces

@[expose] public section


/-!
# Finite dimensionality of `H¹` of a finitely generated group

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open scoped Classical

/-- A crossed homomorphism on a finitely generated group is determined by its values on the generators, hence `H¹` of a finite
dimensional module is finite dimensional. -/
theorem finiteDimensional_H1 {G : Type} [Group G] [Group.FG G] (A : Rep ℂ G) [FiniteDimensional ℂ A] :
    FiniteDimensional ℂ (groupCohomology.H1 A) := by
  obtain ⟨S, hS⟩ := Group.exists_of_isMulFG G
  let φ : groupCohomology.cocycles₁ A →ₗ[ℂ] (S → A) :=
    (LinearMap.pi fun s : S => LinearMap.proj (s : G)).comp (groupCohomology.cocycles₁ A).subtype
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hS0 : ∀ s ∈ S, c.1 s = 0 := fun s hs => congrFun hc ⟨s, hs⟩
    have hcoc := (groupCohomology.mem_cocycles₁_iff c.1).1 c.2
    let K : Subgroup G :=
      { carrier := {g | c.1 g = 0}
        one_mem' := groupCohomology.cocycles₁_map_one c
        mul_mem' := fun {a b} ha hb => by
          show c.1 (a * b) = 0
          have ha' : c.1 a = 0 := ha
          have hb' : c.1 b = 0 := hb
          rw [hcoc, ha', hb', map_zero, add_zero]
        inv_mem' := fun {a} ha => by
          show c.1 a⁻¹ = 0
          have ha' : c.1 a = 0 := ha
          have h := groupCohomology.cocycles₁_map_inv c a
          rw [show c a = 0 from ha', neg_zero] at h
          have h2 := congrArg (A.ρ a⁻¹) h
          rw [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2
          exact h2 }
    have hle : Subgroup.closure (S : Set G) ≤ K := by
      rw [Subgroup.closure_le]
      intro s hs
      exact hS0 s hs
    have htop : (⊤ : Subgroup G) ≤ K := by rw [← hS]; exact hle
    apply Subtype.ext
    funext g
    exact htop (Subgroup.mem_top g)
  have : FiniteDimensional ℂ (groupCohomology.cocycles₁ A) := Module.Finite.of_injective φ hinj
  have hsurj : Function.Surjective (groupCohomology.H1π A).hom := by
    intro x
    induction x using groupCohomology.H1_induction_on with
    | h c => exact ⟨c, rfl⟩
  exact Module.Finite.of_surjective (groupCohomology.H1π A).hom hsurj

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
