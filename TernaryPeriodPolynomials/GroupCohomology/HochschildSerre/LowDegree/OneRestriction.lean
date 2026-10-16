module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.Actions
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

@[expose] public section

open CategoryTheory
noncomputable section
namespace TernaryPoly.LowDegreeHochschildSerre
open groupCohomology
variable {N Q : Type} [Group N] [Group Q] (φ : Q →* MulAut N) (A : Rep ℚ (G φ))

/-- Pointwise cocycle equation with the callable subtype coercion made explicit. -/
theorem one_mul_value (c : cocycles₁ A) (g h : G φ) :
    c (g*h)=A.ρ g (c h)+c g :=
  (mem_cocycles₁_iff _).mp c.property g h

/-- The literal restriction of a one-cocycle to the actual semidirect radical. -/
def restrictOne (c : cocycles₁ A) : cocycles₁ (radicalRep φ A) :=
  ⟨fun n => c (nIn φ n), (mem_cocycles₁_iff _).mpr (by
    intro n m
    simpa using (mem_cocycles₁_iff _).mp c.property (nIn φ n) (nIn φ m))⟩

@[simp] theorem restrictOne_apply (c : cocycles₁ A) (n : N) :
    restrictOne φ A c n=c (nIn φ n) := rfl

/-- Conjugation changes the restricted one-cocycle by the actual coboundary of its Levi value. -/
theorem restrictOne_conjugation (c : cocycles₁ A) (q : Q) :
    (cocyclesOneAction φ A q (restrictOne φ A c) : N → A) -
      (restrictOne φ A c : N → A) = d₀₁ (radicalRep φ A) (c (qIn φ q)) := by
  funext n
  have h := one_mul_value φ A c
  have he : qIn φ q * nIn φ (φ q⁻¹ n) = nIn φ n * qIn φ q := by
    rw [SemidirectProduct.inl_aut]
    simp [mul_assoc]
  have hh := congrArg c he
  rw [h,h] at hh
  change A.ρ (qIn φ q) (c (nIn φ (φ q⁻¹ n))) - c (nIn φ n) =
    A.ρ (nIn φ n) (c (qIn φ q))-c (qIn φ q)
  exact sub_eq_sub_iff_add_eq_add.mpr hh

/-- Every restricted degree-one cohomology class is fixed by the actual Levi action. -/
theorem restrictOne_class_invariant (c : cocycles₁ A) (q : Q) :
    (cohomologyRep φ A 1).ρ q (H1π (radicalRep φ A) (restrictOne φ A c)) =
      H1π (radicalRep φ A) (restrictOne φ A c) := by
  rw [H1π_action]
  apply (H1π_eq_iff _ _).mpr
  rw [restrictOne_conjugation]
  exact ⟨c (qIn φ q),rfl⟩

/-- Vanishing of the genuine invariant radical H1 supplies a coboundary primitive for every
restricted cocycle. The invariant-vanishing premise remains explicit. -/
theorem restrictOne_primitive
    (hvan : ∀ v : groupCohomology (radicalRep φ A) 1,
      (∀ q,(cohomologyRep φ A 1).ρ q v=v) → v=0) (c : cocycles₁ A) :
    ∃ u : A, d₀₁ (radicalRep φ A) u = (restrictOne φ A c : N → A) := by
  have hz := hvan _ (restrictOne_class_invariant φ A c)
  exact (H1π_eq_zero_iff _).mp hz

end TernaryPoly.LowDegreeHochschildSerre
