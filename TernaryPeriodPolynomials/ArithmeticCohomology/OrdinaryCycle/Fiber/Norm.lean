module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.CovectorOrbits

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryFiberNorm
open OrdinaryCovectors OrdinaryCovectorOrbits

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- The literal three-term norm equation on the residue fibers. -/
def norm (α : E →ₗ[ℚ] E) (F : Covector → E) (r : Covector) : E :=
  F r + α (F (stepA (stepA r))) + α (α (F (stepA r)))

/-- Reindexing the three summands propagates a norm equation by A. -/
theorem norm_stepA (α : E →ₗ[ℚ] E) (F : Covector → E)
    (hα : ∀ v,α (α (α v))=v) (r : Covector) :
    norm α F (stepA r)=α (norm α F r) := by
  simp only [norm,stepA_cube,map_add,hα]
  abel

/-- A commuting residue symmetry with an actual coefficient action propagates the norm. -/
theorem norm_commuting (α β : E →ₗ[ℚ] E) (F : Covector → E)
    (d : Covector → Covector)
    (hd : ∀ r,stepA (d r)=d (stepA r))
    (hF : ∀ r,F (d r)=β (F r))
    (hαβ : ∀ v,α (β v)=β (α v)) (r : Covector) :
    norm α F (d r)=β (norm α F r) := by
  simp only [norm,hd,hF,hαβ,map_add]

/-- Exactly five fiber equations suffice, without a polynomial degree bound. -/
theorem all_norms_of_five (α β12 β3 : E →ₗ[ℚ] E) (F : Covector → E)
    (hα : ∀ v,α (α (α v))=v)
    (h12 : ∀ r,F (sign12 r)=β12 (F r))
    (h3 : ∀ r,F (sign3 r)=β3 (F r))
    (hc12 : ∀ v,α (β12 v)=β12 (α v))
    (hc3 : ∀ v,α (β3 v)=β3 (α v))
    (hfive : ∀ i,norm α F (representative i)=0) :
    ∀ r : Covector,r≠0 → norm α F r=0 := by
  apply five_fiber_induction
  · intro r hr
    rw [norm_stepA α F hα,hr,map_zero]
  · intro r hr
    rw [norm_commuting α β12 F sign12 stepA_sign12 h12 hc12,hr,map_zero]
  · intro r hr
    rw [norm_commuting α β3 F sign3 stepA_sign3 h3 hc3,hr,map_zero]
  · exact hfive

end TernaryPoly.OrdinaryFiberNorm
