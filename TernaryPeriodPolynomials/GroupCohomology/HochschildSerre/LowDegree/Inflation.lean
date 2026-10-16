module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.KillCross

@[expose] public section


open CategoryTheory CategoryTheory.Limits groupCohomology
noncomputable section
namespace TernaryPoly.LowDegreeHochschildSerre

variable {N Q : Type} [Group N] [Group Q] (φ : Q →* MulAut N)
variable (A : Rep ℚ (G φ))

/-- The pure quotient values of a mixed-normalized cocycle are actual N-invariants. -/
theorem mixed_invariant (c : cocycles₂ A) (hc : MixedNormalized φ A c) (q r : Q) :
    c (qIn φ q,qIn φ r) ∈ (radicalRep φ A).ρ.invariants := by
  rw [Representation.mem_invariants]
  intro n
  have he := crossCocycle_defect φ A c hc.1 q r n
  simp only [crossCocycle_apply, cocyclesOneAction_apply, hc.2, map_zero, add_zero,
    sub_self] at he
  exact sub_eq_zero.mp he.symm

/-- The literal quotient restriction, valued in A^N. -/
def quotientCocycle (c : cocycles₂ A) (hc : MixedNormalized φ A c) :
    cocycles₂ (invariantsRep φ A) := by
  refine ⟨fun p => ⟨c (qIn φ p.1,qIn φ p.2), mixed_invariant φ A c hc p.1 p.2⟩,
    (mem_cocycles₂_iff _).mpr ?_⟩
  intro q r s
  apply Subtype.ext
  change c (qIn φ (q*r),qIn φ s) + c (qIn φ q,qIn φ r) =
    A.ρ (qIn φ q) (c (qIn φ r,qIn φ s)) + c (qIn φ q,qIn φ (r*s))
  simpa only [map_mul] using
    (mem_cocycles₂_iff c).mp c.property (qIn φ q) (qIn φ r) (qIn φ s)

@[simp] theorem quotientCocycle_apply (c : cocycles₂ A) (hc : MixedNormalized φ A c)
    (q r : Q) : (quotientCocycle φ A c hc (q,r) : (radicalRep φ A).ρ.invariants).val =
      c (qIn φ q,qIn φ r) := rfl

theorem q_mul_n' (q : Q) (n : N) :
    qIn φ q * nIn φ n = nIn φ (φ q n) * qIn φ q := by
  have he := q_mul_n φ q (φ q n)
  simpa only [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    MulAut.one_apply] using he

/-- All values of a mixed-normalized cocycle are the inflation of its quotient restriction. -/
theorem mixed_inflation (c : cocycles₂ A) (hc : MixedNormalized φ A c) (g h : G φ) :
    c (g,h) = c (qIn φ g.right,qIn φ h.right) := by
  have hi (n : N) : A.ρ (nIn φ n) (c (qIn φ g.right,qIn φ h.right)) =
      c (qIn φ g.right,qIn φ h.right) :=
    (Representation.mem_invariants _ _).mp (mixed_invariant φ A c hc _ _) n
  have he := (mem_cocycles₂_iff c).mp c.property
    (qIn φ g.right) (nIn φ h.left) (qIn φ h.right)
  rw [hc.2, hc.1, map_zero, add_zero, zero_add,
    SemidirectProduct.inl_left_mul_inr_right, q_mul_n',
    firstNormalized_equivariance φ A hc.1, hi] at he
  calc
    c (g,h) = c (nIn φ g.left * qIn φ g.right,h) := by
      rw [SemidirectProduct.inl_left_mul_inr_right]
    _ = A.ρ (nIn φ g.left) (c (qIn φ g.right,h)) :=
      firstNormalized_equivariance φ A hc.1 _ _ _
    _ = c (qIn φ g.right,qIn φ h.right) := by rw [← he, hi]

/-- On invariant vectors, the actual semidirect-product action factors through Q. -/
theorem action_invariant (v : (radicalRep φ A).ρ.invariants) (g : G φ) :
    A.ρ g v = A.ρ (qIn φ g.right) v := by
  have hi := (Representation.mem_invariants _ _).mp (invariants_stable φ A g.right v) g.left
  change A.ρ (nIn φ g.left) (A.ρ (qIn φ g.right) v) = _ at hi
  calc
    A.ρ g v = A.ρ (nIn φ g.left * qIn φ g.right) v := by
      rw [SemidirectProduct.inl_left_mul_inr_right]
    _ = A.ρ (qIn φ g.right) v := by simpa only [map_mul, Module.End.mul_apply] using hi

/-- Base H² vanishing kills a mixed-normalized actual cocycle. -/
theorem mixed_class_zero
    (hH2 : IsZero (groupCohomology (invariantsRep φ A) 2))
    (c : cocycles₂ A) (hc : MixedNormalized φ A c) : H2π A c = 0 := by
  have := ModuleCat.isZero_iff_subsingleton.mp hH2
  have hz : H2π (invariantsRep φ A) (quotientCocycle φ A c hc) = 0 := Subsingleton.elim _ _
  obtain ⟨v,hv⟩ := (H2π_eq_zero_iff _).mp hz
  apply (H2π_eq_zero_iff _).mpr
  refine ⟨fun g => (v g.right : (radicalRep φ A).ρ.invariants).val, ?_⟩
  funext ⟨g,h⟩
  have he := congrArg (fun x : (radicalRep φ A).ρ.invariants => x.val)
    (congrFun hv (g.right,h.right))
  change A.ρ (qIn φ g.right) (v h.right : (radicalRep φ A).ρ.invariants).val -
    (v (g.right*h.right) : (radicalRep φ A).ρ.invariants).val +
    (v g.right : (radicalRep φ A).ρ.invariants).val = c (qIn φ g.right,qIn φ h.right) at he
  change A.ρ g (v h.right : (radicalRep φ A).ρ.invariants).val -
    (v (g.right*h.right) : (radicalRep φ A).ρ.invariants).val +
    (v g.right : (radicalRep φ A).ρ.invariants).val = c (g,h)
  rw [action_invariant, mixed_inflation φ A c hc]
  exact he

end TernaryPoly.LowDegreeHochschildSerre
