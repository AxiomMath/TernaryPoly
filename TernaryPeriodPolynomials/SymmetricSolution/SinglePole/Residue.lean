module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Module

@[expose] public section

open MvPolynomial
open scoped DirectSum
noncomputable section
namespace TernaryPoly.SinglePole
attribute [local instance] Classical.propDecidable

/-- Prime cancellation proves that relations between rational functions have zero residues. -/
theorem presentation_kernel_le (n : ℕ) :
    (presentationMap n).ker ≤ (presentationResidues n).ker := by
  intro p hp
  change presentationMap n p = 0 at hp
  change presentationResidues n p = 0
  apply DFinsupp.ext
  intro H
  change (numeratorRelations n H).mkQ (p.2 H) = 0
  by_cases hH : H ∈ p.2.support
  · apply (residueFiber_eq_zero_iff n H (p.2 H)).mpr
    apply normal_denominator_cancellation p.2.support (fun J => (p.2 J).val) (-p.1.val) _ H hH
    rw [map_neg]
    apply eq_neg_iff_add_eq_zero.mpr
    rw [presentationMap_apply,polynomialMap_apply,poleSum_apply] at hp
    simpa only [add_comm] using hp
  · have hpH : p.2 H = 0 := by simpa only [DFinsupp.mem_support_iff,not_not] using hH
    rw [hpH,map_zero]

/-- Equal rational functions have equal finite principal-part vectors. -/
theorem presentation_residues_eq (n : ℕ) (p q : Presentation n)
    (h : presentationMap n p = presentationMap n q) :
    presentationResidues n p = presentationResidues n q := by
  have hf : p - q ∈ (presentationMap n).ker := by
    change presentationMap n (p - q) = 0
    rw [(presentationMap n).map_sub,h,sub_self]
  have hg := presentation_kernel_le n hf
  change presentationResidues n (p - q) = 0 at hg
  rw [(presentationResidues n).map_sub,sub_eq_zero] at hg
  exact hg

/-- A finite presentation of an actual fraction-field element in the image. -/
def representative (n : ℕ) (x : singlePole n) : Presentation n := x.property.choose

theorem representative_spec (n : ℕ) (x : singlePole n) :
    presentationMap n (representative n x) = x.val := x.property.choose_spec

/-- Actual residues; prime cancellation makes the representative choice immaterial. -/
def residue (n : ℕ) : singlePole n →ₗ[ℚ] Residues n where
  toFun x := presentationResidues n (representative n x)
  map_add' x y := by
    rw [← map_add]
    apply presentation_residues_eq
    rw [map_add,representative_spec,representative_spec,representative_spec]
    rfl
  map_smul' c x := by
    rw [RingHom.id_apply,← map_smul]
    apply presentation_residues_eq
    rw [map_smul,representative_spec,representative_spec]
    rfl

/-- Evaluation of any finite presentation gives the same actual residue vector. -/
theorem residue_presentation (n : ℕ) (p : Presentation n) :
    residue n ((presentationMap n).rangeRestrict p) = presentationResidues n p := by
  apply presentation_residues_eq
  exact representative_spec n ((presentationMap n).rangeRestrict p)

/-- In particular, the original homogeneous polynomials have zero principal part. -/
theorem residue_polynomial (n : ℕ) (p : V n) : residue n (polynomialInclusion n p) = 0 := by
  change residue n ((presentationMap n).rangeRestrict (p,0)) = 0
  rw [residue_presentation]
  exact map_zero (numeratorResidues n)

/-- Zero residues cancel separately to an actual degree-n polynomial. -/
theorem presentation_regular (n : ℕ) (p : Presentation n)
    (hp : presentationResidues n p = 0) :
    ∃ q : V n, presentationMap n p = polynomialMap n q := by
  have hq : ∀ H, ∃ q : V n, denominator H * q.val = (p.2 H).val := by
    intro H
    have he := congrArg (fun r : Residues n => r H) hp
    change (numeratorRelations n H).mkQ (p.2 H) = 0 at he
    exact homogeneous_divisor (denominator_homogeneous H) (p.2 H).property
      ((residueFiber_eq_zero_iff n H (p.2 H)).mp he)
  choose q hq using hq
  refine ⟨p.1 + ∑ H ∈ p.2.support, q H, ?_⟩
  rw [presentationMap_apply,map_add,map_sum]
  congr 1
  rw [poleSum_apply]
  apply Finset.sum_congr rfl
  intro H _
  rw [← hq H,map_mul,polynomialMap_apply]
  exact mul_div_cancel_left₀ _ (embed_ne_zero.mpr (denominator_ne_zero H))

/-- The kernel is precisely the embedded homogeneous polynomial subspace. -/
theorem residue_exact (n : ℕ) : (residue n).ker = (polynomialInclusion n).range := by
  apply le_antisymm
  · intro x hx
    obtain ⟨p,hp⟩ := x.property
    have hex : (presentationMap n).rangeRestrict p = x := Subtype.ext hp
    have hres : presentationResidues n p = 0 := by
      rw [← residue_presentation,hex]
      exact hx
    obtain ⟨q,hq⟩ := presentation_regular n p hres
    refine ⟨q,Subtype.ext ?_⟩
    rw [polynomialInclusion_val]
    exact hq.symm.trans hp
  · rintro x ⟨p,rfl⟩
    exact residue_polynomial n p

/-- Every finite-support principal-part family has an actual single-pole rational lift. -/
theorem residue_surjective (n : ℕ) : Function.Surjective (residue n) := by
  intro r
  obtain ⟨p,hp⟩ := numeratorResidues_surjective n r
  refine ⟨(presentationMap n).rangeRestrict (0,p), ?_⟩
  rw [residue_presentation]
  exact hp

/-- Concrete linear exactness, including both endpoint properties. -/
theorem residue_short_exact (n : ℕ) :
    Function.Injective (polynomialInclusion n) ∧
      (residue n).ker = (polynomialInclusion n).range ∧ Function.Surjective (residue n) :=
  ⟨polynomialInclusion_injective n,residue_exact n,residue_surjective n⟩

end TernaryPoly.SinglePole
