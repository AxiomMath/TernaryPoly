module

public import TernaryPeriodPolynomials.PeriodPolynomial.Apolar.Powers
public import Mathlib.Algebra.CharZero.Infinite

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryApolar
open BinaryHomogeneous
variable (K : Type*) [Field K] [CharZero K]

/-- The actual nondegenerate contraction identifies the homogeneous space with its dual. -/
theorem form_surjective (d : ℕ) : Function.Surjective (form K d) := by
  let : FiniteDimensional K (H K d) :=
    FiniteDimensional.of_injective (coefficientEquiv K d).toLinearMap
      (coefficientEquiv K d).injective
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := K) (V := H K d)).symm).mp
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  apply separating_left K d p
  intro q
  exact congrArg (fun f : Module.Dual K (H K d) => f q) hp

/-- Vanishing against all actual pure powers forces the polynomial itself to vanish. -/
theorem eq_zero_of_form_pure (d : ℕ) (p : H K d)
    (hp : ∀ a b,form K d p (pure K d a b)=0) : p=0 := by
  apply Subtype.ext
  change p.val=0
  apply p.property.eq_zero_of_forall_eval_eq_zero
  intro r
  have h := hp (r 1) (-r 0)
  rw [form_pure,neg_neg] at h
  have hr : (![r 0,r 1] : Fin 2 → K)=r := by
    funext j
    fin_cases j <;> rfl
  simpa only [hr] using h

/-- Pure powers span every actual homogeneous binary polynomial, uniformly in degree. -/
theorem span_pure (d : ℕ) :
    Submodule.span K (Set.range (fun v : K×K => pure K d v.1 v.2))=⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro φ hφ
  obtain ⟨p,rfl⟩ := form_surjective K d φ
  have hp : p=0 := by
    apply eq_zero_of_form_pure K d p
    intro a b
    exact (Submodule.mem_dualAnnihilator _).mp hφ _
      (Submodule.subset_span ⟨(a,b),rfl⟩)
  simp [hp]

end TernaryPoly.BinaryApolar
