module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.Normalize

@[expose] public section


open CategoryTheory CategoryTheory.Limits groupCohomology
noncomputable section
namespace TernaryPoly.LowDegreeHochschildSerre

variable {N Q : Type} [Group N] [Group Q] (φ : Q →* MulAut N)
variable (A : Rep ℚ (G φ))

/-- The actual cross one-cocycle associated to a first-normalized two-cocycle. -/
def crossCocycle (c : cocycles₂ A) (hc : FirstNormalized φ A c) (q : Q) :
    cocycles₁ (radicalRep φ A) := by
  refine ⟨fun n => c (qIn φ q,nIn φ (φ q⁻¹ n)), (mem_cocycles₁_iff _).mpr ?_⟩
  intro n m
  have he := restriction_conjugation_difference φ A c q n m
  simp only [hc, map_zero, sub_zero] at he
  change _ = A.ρ (nIn φ n) _ + _
  linear_combination (norm := module) he

@[simp] theorem crossCocycle_apply (c : cocycles₂ A) (hc : FirstNormalized φ A c)
    (q : Q) (n : N) : crossCocycle φ A c hc q n =
      c (qIn φ q,nIn φ (φ q⁻¹ n)) := rfl

/-- The failure of the cross cocycles to form a Q-cocycle is an actual principal N-cocycle. -/
theorem crossCocycle_defect (c : cocycles₂ A) (hc : FirstNormalized φ A c)
    (q r : Q) (n : N) :
    crossCocycle φ A c hc (q*r) n -
      (cocyclesOneAction φ A q (crossCocycle φ A c hc r) n +
        crossCocycle φ A c hc q n) =
      A.ρ (nIn φ n) (c (qIn φ q,qIn φ r)) - c (qIn φ q,qIn φ r) := by
  have h₁ := (mem_cocycles₂_iff c).mp c.property
    (qIn φ q) (qIn φ r) (nIn φ (φ r⁻¹ (φ q⁻¹ n)))
  have h₂ := (mem_cocycles₂_iff c).mp c.property
    (qIn φ q) (nIn φ (φ q⁻¹ n)) (qIn φ r)
  rw [q_mul_n, firstNormalized_equivariance φ A hc, hc, map_zero, zero_add] at h₂
  rw [q_mul_n, ← map_mul] at h₁
  simp only [crossCocycle_apply, cocyclesOneAction_apply, mul_inv_rev, map_mul φ,
    MulAut.mul_apply]
  linear_combination (norm := module) h₁ - h₂

/-- Passing the actual cross cocycles to H¹(N,A) gives an actual Q one-cocycle. -/
def crossClass (c : cocycles₂ A) (hc : FirstNormalized φ A c) :
    cocycles₁ (cohomologyRep φ A 1) := by
  refine ⟨fun q => H1π (radicalRep φ A) (crossCocycle φ A c hc q),
    (mem_cocycles₁_iff _).mpr ?_⟩
  intro q r
  rw [H1π_action, ← map_add]
  apply (H1π_eq_iff _ _).mpr
  refine ⟨c (qIn φ q,qIn φ r), ?_⟩
  funext n
  exact (crossCocycle_defect φ A c hc q r n).symm

@[simp] theorem crossClass_apply (c : cocycles₂ A) (hc : FirstNormalized φ A c) (q : Q) :
    crossClass φ A c hc q = H1π (radicalRep φ A) (crossCocycle φ A c hc q) := rfl

end TernaryPoly.LowDegreeHochschildSerre
