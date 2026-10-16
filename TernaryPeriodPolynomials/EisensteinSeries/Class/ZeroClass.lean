module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ZigZagMain

@[expose] public section


/-!
# A closed equivariant form with an equivariant primitive has zero class

(the class of an invariant form on `Γ_P \\ e(P)` that is exact among invariant forms is zero).

If `ω ∈ invClosed hs A ρ` is the differential `dη` of a form `η` which is itself `ρ`-equivariant
(`g^*η = ρ(g)η`), then the zig-zag datum `(η, θ_g = 0)` has zero cochain, so `deRhamClass ω = 0`
(`deRhamClass_eq_zero_of_equivariant_primitive`). This is the sufficient condition used to reduce the
vanishing of the non-identity part of the constant term to a statement about forms.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology
open TernaryPoly.SmoothLocalDeRham

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
  {s : Set E} {G : Type} [Group G]

/-- **An equivariant primitive kills the class.** -/
theorem deRhamClass_eq_zero_of_equivariant_primitive (hs : IsOpen s) (hc : Convex ℝ s)
    (hne : s.Nonempty) (A : Action G s) (ρ : Representation ℝ G F) (om : invClosed hs A ρ)
    (η : Form (F := F) s 1) (hη : d hs 1 η = (om : Form (F := F) s 2))
    (hinv : ∀ g, pullForm hs A g 1 η = twForm (repCLM ρ g) 1 η) :
    deRhamClass hs hc hne A ρ om = 0 := by
  let D : Datum (d hs 0) (d hs 1) (fun g => pullForm hs A g 1)
      (fun g => twForm (repCLM ρ g) 1) (om : Form (F := F) s 2) :=
    ⟨η, fun _ => 0, hη, fun g => by simp [hinv g]⟩
  rw [deRhamClass_eq hs hc hne A ρ om D]
  have hz : ∀ g k, cochain (laws hs hc hne A ρ) D g k = 0 := by
    intro g k
    apply (laws hs hc hne A ρ).c_injective
    rw [c_cochain (laws hs hc hne A ρ) D g k]
    simp [D]
  have : cochainCocycle (laws hs hc hne A ρ) D = 0 := by
    apply Subtype.ext
    funext p
    exact hz p.1 p.2
  unfold zigzagClass
  rw [this, map_zero]

end TernaryPeriodPolynomials.Argument.EisensteinClass
