module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.OneRestriction

@[expose] public section


open CategoryTheory
noncomputable section
namespace TernaryPoly.LowDegreeHochschildSerre
open groupCohomology
variable {N Q : Type} [Group N] [Group Q] (φ : Q →* MulAut N) (A : Rep ℚ (G φ))

/-- A cocycle zero on the radical is constant along its actual quotient fibers. -/
theorem one_value_quotient (c : cocycles₁ A) (hc : ∀ n,c (nIn φ n)=0) (g : G φ) :
    c g=c (qIn φ g.right) := by
  have he : g=qIn φ g.right*nIn φ (φ g.right⁻¹ g.left) := by
    rw [SemidirectProduct.inl_aut]
    simp [mul_assoc]
  calc
    c g = c (qIn φ g.right*nIn φ (φ g.right⁻¹ g.left)) := congrArg c he
    _ = c (qIn φ g.right) := by rw [one_mul_value φ A c,hc,map_zero,zero_add]

/-- Its Levi values are genuine radical-invariant coefficient vectors. -/
theorem one_value_invariants (c : cocycles₁ A) (hc : ∀ n,c (nIn φ n)=0) (q : Q) :
    c (qIn φ q) ∈ (radicalRep φ A).ρ.invariants := by
  intro n
  have hh := one_mul_value φ A c (nIn φ n) (qIn φ q)
  rw [one_value_quotient φ A c hc,hc,add_zero] at hh
  simpa [nIn,qIn] using hh.symm

/-- The quotient restriction is an actual cocycle with values in A^N. -/
def quotientOne (c : cocycles₁ A) (hc : ∀ n,c (nIn φ n)=0) :
    cocycles₁ (invariantsRep φ A) :=
  ⟨fun q => ⟨c (qIn φ q),one_value_invariants φ A c hc q⟩,
    (mem_cocycles₁_iff _).mpr (by
      intro q r
      apply Subtype.ext
      change c (qIn φ (q*r))=A.ρ (qIn φ q) (c (qIn φ r))+c (qIn φ q)
      rw [map_mul,one_mul_value φ A c])⟩

@[simp] theorem quotientOne_apply (c : cocycles₁ A) (hc : ∀ n,c (nIn φ n)=0) (q : Q) :
    (quotientOne φ A c hc q : A)=c (qIn φ q) := rfl

/-- The degree-one inflation normal form, constructed on genuine cochains. Every cocycle differs
by an actual coboundary from an inflated cocycle with radical-invariant values. -/
theorem exists_inflated_one
    (hvan : ∀ v : groupCohomology (radicalRep φ A) 1,
      (∀ q,(cohomologyRep φ A 1).ρ q v=v) → v=0) (c : cocycles₁ A) :
    ∃ (u : A) (b : cocycles₁ (invariantsRep φ A)),
      ∀ g : G φ,c g = (d₀₁ A u) g+(b g.right : A) := by
  obtain ⟨u,hu⟩ := restrictOne_primitive φ A hvan c
  let c' : cocycles₁ A := c-⟨d₀₁ A u,d₀₁_apply_mem_cocycles₁ (A := A) u⟩
  have hc' : ∀ n,c' (nIn φ n)=0 := by
    intro n
    have hh := congrFun hu n
    change c (nIn φ n)-(d₀₁ A u) (nIn φ n)=0
    change (d₀₁ A u) (nIn φ n)=c (nIn φ n) at hh
    exact sub_eq_zero.mpr hh.symm
  refine ⟨u,quotientOne φ A c' hc',?_⟩
  intro g
  have hg := one_value_quotient φ A c' hc' g
  change c g-(d₀₁ A u) g=c' (qIn φ g.right) at hg
  change c g=(d₀₁ A u) g+c' (qIn φ g.right)
  exact (sub_eq_iff_eq_add.mp hg).trans (add_comm _ _)

end TernaryPoly.LowDegreeHochschildSerre
