module

public import TernaryPeriodPolynomials.PeriodPolynomial.Apolar.FiniteOperators
public import TernaryPeriodPolynomials.PeriodPolynomial.FiniteInvariant.Projectors

@[expose] public section

noncomputable section
namespace TernaryPoly.BinaryApolar
open BinaryFiniteInvariant

/-- The order-three norm is self-adjoint. -/
theorem norm_adjoint (d : ℕ) (p q : H d) :
    form ℚ d (norm d p) q=form ℚ d p (norm d q) := by
  simp only [norm_apply,map_add,LinearMap.add_apply]
  rw [rotation_adjoint,rotation_adjoint,rotation_adjoint]
  rw [rotation_rotation_rotation]
  ring

/-- The two-involution average is self-adjoint in even degree. -/
theorem oddProjector_adjoint (d : ℕ) (hd : Even d) (p q : H d) :
    form ℚ d (oddProjector d p) q=form ℚ d p (oddProjector d q) := by
  simp only [oddProjector_apply,map_smul,map_sub,map_add,LinearMap.smul_apply,
    LinearMap.sub_apply,LinearMap.add_apply,smul_eq_mul]
  rw [swap_adjoint d hd,negateFirst_adjoint d hd,swap_adjoint d hd,negateFirst_adjoint d hd,
    negateFirst_swap d hd]

/-- The actual six-term invariant average is self-adjoint in even degree. -/
theorem invariantProjector_adjoint (d : ℕ) (hd : Even d) (p q : H d) :
    form ℚ d (invariantProjector d p) q=form ℚ d p (invariantProjector d q) := by
  simp only [invariantProjector_apply,map_smul,map_add,LinearMap.smul_apply,
    LinearMap.add_apply,smul_eq_mul]
  rw [norm_adjoint,swap_adjoint d hd,norm_adjoint]
  rw [show norm d (swap d q)=swap d (norm d q) from
    (LinearMap.congr_fun (swap_norm d) q).symm]

/-- Apolarity restricted to the genuine odd symmetric subspace is separating. -/
theorem oddSymmetric_separating (d : ℕ) (hd : Even d) (p : oddSymmetric d)
    (hp : ∀ q : oddSymmetric d,form ℚ d p.val q.val=0) : p=0 := by
  apply Subtype.ext
  apply separating_left ℚ d p.val
  intro v
  have hfix := (oddProjector_isProj d hd).map_id p.val p.property
  rw [←hfix,oddProjector_adjoint d hd]
  exact hp ⟨oddProjector d v,(oddProjector_isProj d hd).map_mem v⟩

/-- Apolarity restricted to the finite-group invariant subspace is separating. -/
theorem invariants_separating (d : ℕ) (hd : Even d) (p : invariants d)
    (hp : ∀ q : invariants d,form ℚ d p.val q.val=0) : p=0 := by
  apply Subtype.ext
  apply separating_left ℚ d p.val
  intro v
  have hfix := (invariantProjector_isProj d).map_id p.val p.property
  rw [←hfix,invariantProjector_adjoint d hd]
  exact hp ⟨invariantProjector d v,(invariantProjector_isProj d).map_mem v⟩

/-- The same restricted pairing is separating in its second argument. -/
theorem oddSymmetric_separating_right (d : ℕ) (hd : Even d) (p : oddSymmetric d)
    (hp : ∀ q : oddSymmetric d,form ℚ d q.val p.val=0) : p=0 := by
  apply Subtype.ext
  apply separating_right ℚ d p.val
  intro v
  have hfix := (oddProjector_isProj d hd).map_id p.val p.property
  rw [←hfix,←oddProjector_adjoint d hd]
  exact hp ⟨oddProjector d v,(oddProjector_isProj d hd).map_mem v⟩

theorem invariants_separating_right (d : ℕ) (hd : Even d) (p : invariants d)
    (hp : ∀ q : invariants d,form ℚ d q.val p.val=0) : p=0 := by
  apply Subtype.ext
  apply separating_right ℚ d p.val
  intro v
  have hfix := (invariantProjector_isProj d).map_id p.val p.property
  rw [←hfix,←invariantProjector_adjoint d hd]
  exact hp ⟨invariantProjector d v,(invariantProjector_isProj d).map_mem v⟩

end TernaryPoly.BinaryApolar
