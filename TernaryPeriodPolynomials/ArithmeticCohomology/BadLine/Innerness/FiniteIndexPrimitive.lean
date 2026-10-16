module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.GoodPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.FiniteAveraging

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem cocycle_primitive_of_finite_index (ambient source target : Subgroup G)
    [Fintype (target ⧸ source.subgroupOf target)] (inclusion : target ≤ ambient)
    (representation : Representation ℂ G V) (cocycle : cocycles ambient representation)
    (primitive : cochains source representation 1)
    (primitive_eq : ∀ vertices, (differentialOne source representation primitive).val vertices =
      cocycle.val.val vertices) :
    ∃ result : cochains target representation 1, ∀ vertices,
      (differentialOne target representation result).val vertices = cocycle.val.val vertices := by
  classical
  let Q := target ⧸ source.subgroupOf target
  let term : Q → (Fin 2 → G) → V := fun q vertices =>
    representation q.out.val (primitive.val (fun i => q.out.val⁻¹*vertices i))
  have diagonal (h : target) (q : Q) (vertices : Fin 2 → G) :
      term (h • q) (fun i => h.val*vertices i) = representation h.val (term q vertices) := by
    have representatives : (QuotientGroup.mk (h • q).out : Q) =
        QuotientGroup.mk (h*q.out) := by
      rw [QuotientGroup.out_eq']
      have moved := congrArg (fun r : Q => h • r) (QuotientGroup.out_eq' q)
      exact moved.symm
    have member := QuotientGroup.eq.mp representatives
    let correction : source := ⟨(h • q).out.val⁻¹*h.val*q.out.val,by
      change ((h • q).out⁻¹*(h*q.out)).val ∈ source at member
      simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc] using member⟩
    have shifted : (fun i => correction.val*(q.out.val⁻¹*vertices i)) =
        (fun i => (h • q).out.val⁻¹*(h.val*vertices i)) := by
      funext i
      simp only [correction,mul_assoc,mul_inv_cancel_left]
    have equivariance := primitive.property correction (fun i => q.out.val⁻¹*vertices i)
    rw [shifted] at equivariance
    change representation (h • q).out.val
      (primitive.val (fun i => (h • q).out.val⁻¹*(h.val*vertices i))) = _
    rw [equivariance,← Module.End.mul_apply,← map_mul]
    have product_eq : (h • q).out.val*correction.val = h.val*q.out.val := by
      simp only [correction,← mul_assoc,mul_inv_cancel,one_mul]
    rw [product_eq,map_mul,Module.End.mul_apply]
  let result : cochains target representation 1 := ⟨fun vertices =>
    (Fintype.card Q : ℂ)⁻¹ • ∑ q, term q vertices,by
      intro h vertices
      change (Fintype.card Q : ℂ)⁻¹ • ∑ q, term q (fun i => h.val*vertices i) =
        representation h.val ((Fintype.card Q : ℂ)⁻¹ • ∑ q, term q vertices)
      rw [← Equiv.sum_comp (MulAction.toPerm h) (fun q : Q => term q (fun i => h.val*vertices i))]
      simp only [MulAction.toPerm_apply,diagonal,← map_sum,← map_smul]⟩
  refine ⟨result,?_⟩
  intro vertices
  have term_boundary (q : Q) :
      term q ![vertices 1,vertices 2]-term q ![vertices 0,vertices 2]+term q ![vertices 0,vertices 1] =
        cocycle.val.val vertices := by
    have pair_eq (a b : G) : (fun i => q.out.val⁻¹*![a,b] i) =
        ![q.out.val⁻¹*a,q.out.val⁻¹*b] := by
      funext i
      fin_cases i <;> rfl
    simp only [term,pair_eq,← map_sub,← map_add]
    change representation q.out.val
      ((differentialOne source representation primitive).val (fun i => q.out.val⁻¹*vertices i)) = _
    rw [primitive_eq]
    have equivariance := cocycle.val.property ⟨q.out.val,inclusion q.out.property⟩
      (fun i => q.out.val⁻¹*vertices i)
    simpa only [mul_inv_cancel_left] using equivariance.symm
  change (Fintype.card Q : ℂ)⁻¹ • ∑ q, term q ![vertices 1,vertices 2] -
      (Fintype.card Q : ℂ)⁻¹ • ∑ q, term q ![vertices 0,vertices 2] +
      (Fintype.card Q : ℂ)⁻¹ • ∑ q, term q ![vertices 0,vertices 1] = _
  rw [← smul_sub,← smul_add,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  simp only [term_boundary,Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  have nonzero : (Fintype.card Q : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ nonzero,one_smul]

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
