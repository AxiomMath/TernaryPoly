module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ZigZagClass
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ZigZagDeRham

@[expose] public section


/-!
# The de Rham class map for a group acting on a convex open set

For a group `G` acting by smooth maps on a nonempty convex open set `s` of a finite-dimensional
real normed space, and a finite-dimensional real representation `ρ` of `G` (the coefficients), the
closed `ρ`-equivariant 2-forms on `s` map linearly to `H²(G, F)`, by the zig-zag of `ZigZagAlgebra`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology
open TernaryPoly.SmoothLocalDeRham

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
  {s : Set E} {G : Type} [Group G]

/-- Closed, `ρ`-equivariant `F`-valued 2-forms on `s`: `dω = 0` and `g^*ω = ρ(g)ω`. -/
def invClosed (hs : IsOpen s) (A : Action G s) (ρ : Representation ℝ G F) :
    Submodule ℝ (Form (F := F) s 2) where
  carrier := {om | d hs 2 om = 0 ∧ ∀ g, pullForm hs A g 2 om = twForm (repCLM ρ g) 2 om}
  zero_mem' := ⟨map_zero _, fun g => by rw [map_zero, map_zero]⟩
  add_mem' := fun {a b} ha hb => ⟨by rw [map_add, ha.1, hb.1, add_zero],
    fun g => by rw [map_add, map_add, ha.2 g, hb.2 g]⟩
  smul_mem' := fun c {a} ha => ⟨by rw [map_smul, ha.1, smul_zero],
    fun g => by rw [map_smul, map_smul, ha.2 g]⟩

/-- Zig-zag data for every closed equivariant 2-form. -/
theorem exists_datum_deRham (hs : IsOpen s) (hc : Convex ℝ s) (hne : s.Nonempty)
    (A : Action G s) (ρ : Representation ℝ G F) (om : invClosed hs A ρ) :
    Nonempty (Datum (d hs 0) (d hs 1) (fun g => pullForm hs A g 1)
      (fun g => twForm (repCLM ρ g) 1) (om : Form (F := F) s 2)) :=
  exists_datum (laws hs hc hne A ρ) (fun om => d hs 2 om = 0) (exact2 hs hc) om.2.1 om.2.2

/-- **The de Rham class map**: closed equivariant 2-forms on a convex open set to `H²(G, F)`. -/
def deRhamClass (hs : IsOpen s) (hc : Convex ℝ s) (hne : s.Nonempty) (A : Action G s)
    (ρ : Representation ℝ G F) : invClosed hs A ρ →ₗ[ℝ] H2 (Rep.of ρ) where
  toFun om := zigzagClass (laws hs hc hne A ρ)
    (Classical.choice (exists_datum_deRham hs hc hne A ρ om))
  map_add' om om' := by
    rw [← zigzagClass_add]
    exact zigzagClass_indep _ _ _
  map_smul' a om := by
    rw [← zigzagClass_smul]
    exact zigzagClass_indep _ _ _

/-- The class of a form is the class of ANY zig-zag datum for it. -/
theorem deRhamClass_eq (hs : IsOpen s) (hc : Convex ℝ s) (hne : s.Nonempty) (A : Action G s)
    (ρ : Representation ℝ G F) (om : invClosed hs A ρ)
    (D : Datum (d hs 0) (d hs 1) (fun g => pullForm hs A g 1)
      (fun g => twForm (repCLM ρ g) 1) (om : Form (F := F) s 2)) :
    deRhamClass hs hc hne A ρ om = zigzagClass (laws hs hc hne A ρ) D :=
  zigzagClass_indep _ _ _

end TernaryPeriodPolynomials.Argument.SeedC3.ZigZag
