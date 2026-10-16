module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticPlaneBounds
public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticSiegelAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceBorelCorner
open SymmetricSpaceRationalGluing SymmetricSpaceRationalAction SymmetricSpaceLineBordification
open SymmetricSpaceCornerSeparation SymmetricSpaceCornerDegeneration

/-- Inverting an actual relative arithmetic matrix swaps the two frames. -/
theorem relative_inv (a b : RationalGL) (g : IntegralGL) :
    (relative a b g)⁻¹=relative b a g⁻¹ := by
  simp [relative,map_inv,mul_assoc]

/-- The actual dual matrix entries are precisely the reversed transpose inverse entries. -/
theorem dualGL_entry (r : RealGL) (i j : Fin 3) :
    (dualGL r).val i j=r⁻¹.val j.rev i.rev := by
  fin_cases i <;> fin_cases j <;>
    simp [dualGL,contragredient,flipGL,flipMatrix,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

theorem dualGL_hasIntegralDenominator (d : ℕ) (r : RealGL)
    (h : HasIntegralDenominator d r⁻¹) : HasIntegralDenominator d (dualGL r) := by
  intro i j
  rw [dualGL_entry]
  exact h j.rev i.rev

theorem dualGL_det_abs (r : RealGL) : |(dualGL r).val.det|=|r⁻¹.val.det| := by
  change |(flipMatrix*star r⁻¹.val*flipMatrix).det|=_
  rw [det_mul,det_mul,Matrix.star_eq_conjTranspose,det_conjTranspose]
  simp [flipMatrix,det_fin_three]

/-- Actual full transition graphs are preserved by inverse matrix and swapped endpoints. -/
theorem fullGraph_inv (r : RealGL) {p q : Corner} (h : (p,q)∈fullGraph r) :
    (q,p)∈fullGraph r⁻¹ := by
  rw [fullGraph_eq_closure_interior] at h ⊢
  apply map_mem_closure continuous_swap h
  rintro z ⟨S,hp,hq⟩
  refine ⟨act r S,hq,?_⟩
  change z.1=cornerEmbedding (act r⁻¹ (act r S))
  rw [←act_mul,inv_mul_cancel,act_one]
  exact hp

/-- Actual full transition graphs commute with the corner and inverse-form duality. -/
theorem fullGraph_dual (r : RealGL) {p q : Corner} (h : (p,q)∈fullGraph r) :
    (dualCorner p,dualCorner q)∈fullGraph (dualGL r) := by
  rw [fullGraph_eq_closure_interior] at h ⊢
  apply map_mem_closure (dualCornerHomeomorph.continuous.prodMap dualCornerHomeomorph.continuous) h
  rintro z ⟨S,hp,hq⟩
  refine ⟨dualForm S,?_,?_⟩
  · change dualCorner z.1=cornerEmbedding (dualForm S)
    rw [hp,dualCorner_embedding]
  · change dualCorner z.2=cornerEmbedding (act (dualGL r) (dualForm S))
    rw [hq,dualCorner_embedding,dualForm_act]

/-- The polynomial corner duality sends a bounded shear box to an explicitly bounded shear box. -/
theorem dualCorner_coordinate_bound (M : ℝ) (hM : 0≤M) (p : Corner)
    (hp : ∀ i,|p.1 i|≤M) : ∀ i,|(dualCorner p).1 i|≤M^2+M := by
  have hMN : M≤M^2+M := by nlinarith only [sq_nonneg M]
  intro i
  fin_cases i
  · change |-p.1 1|≤M^2+M
    rw [abs_neg]
    exact (hp 1).trans hMN
  · change |-p.1 0|≤M^2+M
    rw [abs_neg]
    exact (hp 0).trans hMN
  · change |p.1 0*p.1 1-p.1 2|≤M^2+M
    apply (abs_sub _ _).trans
    apply add_le_add _ (hp 2)
    rw [abs_mul,pow_two]
    exact mul_le_mul (hp 0) (hp 1) (abs_nonneg _) hM

end TernaryPoly.SymmetricSpaceGluedArithmetic
