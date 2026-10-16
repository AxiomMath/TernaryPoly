module

public import TernaryPeriodPolynomials.SymmetricSpace.Borel.CornerAlgebra

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBorelCorner
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates SymmetricSpaceFlagCoordinates
open Topology

/-- The exact signed Borel formulas extend to both zero-root faces of the existing closed corner. -/
def extend (g : BorelGroup) (p : Corner) : Corner :=
  (shear g p.1,(⟨factor1 g*p.2.1.val,by
    change 0≤factor1 g*p.2.1.val
    exact mul_nonneg (factor1_pos g).le p.2.1.property⟩,
    ⟨factor2 g*p.2.2.val,by
      change 0≤factor2 g*p.2.2.val
      exact mul_nonneg (factor2_pos g).le p.2.2.property⟩))

@[simp] theorem extend_x (g : BorelGroup) (p : Corner) :
    (extend g p).1 0=(g.val.val 0 0*p.1 0+g.val.val 0 1)/g.val.val 1 1 := rfl
@[simp] theorem extend_y (g : BorelGroup) (p : Corner) :
    (extend g p).1 1=(g.val.val 1 1*p.1 1+g.val.val 1 2)/g.val.val 2 2 := rfl
@[simp] theorem extend_z (g : BorelGroup) (p : Corner) :
    (extend g p).1 2=(g.val.val 0 0*p.1 2+g.val.val 0 1*p.1 1+g.val.val 0 2)/g.val.val 2 2 := rfl
@[simp] theorem extend_t1 (g : BorelGroup) (p : Corner) :
    (extend g p).2.1.val=|g.val.val 1 1/g.val.val 0 0| * p.2.1.val := rfl
@[simp] theorem extend_t2 (g : BorelGroup) (p : Corner) :
    (extend g p).2.2.val=|g.val.val 2 2/g.val.val 1 1| * p.2.2.val := rfl

theorem continuous_shear_joint : Continuous (fun z : BorelGroup × Vec3 => shear z.1 z.2) := by
  have hg (i j : Fin 3) : Continuous (fun z : BorelGroup × Vec3 => z.1.val.val i j) :=
    (continuous_entry i j).comp continuous_fst
  have hv (i : Fin 3) : Continuous (fun z : BorelGroup × Vec3 => z.2 i) :=
    (continuous_apply i).comp continuous_snd
  apply continuous_pi
  intro i
  fin_cases i
  · exact ((hg 0 0 |>.mul (hv 0)).add (hg 0 1)).div₀ (hg 1 1)
      (fun z => (diagonal_nonzero z.1).2.1)
  · exact ((hg 1 1 |>.mul (hv 1)).add (hg 1 2)).div₀ (hg 2 2)
      (fun z => (diagonal_nonzero z.1).2.2)
  · exact (((hg 0 0 |>.mul (hv 2)).add (hg 0 1 |>.mul (hv 1))).add (hg 0 2)).div₀ (hg 2 2)
      (fun z => (diagonal_nonzero z.1).2.2)

theorem continuous_extend_joint : Continuous (fun z : BorelGroup × Corner => extend z.1 z.2) := by
  apply Continuous.prodMk
  · exact continuous_shear_joint.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  · apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact (continuous_factor1.comp continuous_fst).mul
        (continuous_subtype_val.comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))
    · apply Continuous.subtype_mk
      exact (continuous_factor2.comp continuous_fst).mul
        (continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))

theorem continuous_extend (g : BorelGroup) : Continuous (extend g) :=
  continuous_extend_joint.comp (continuous_const.prodMk continuous_id)

/-- The boundary extension agrees with the actual normalized congruence embedding. -/
theorem extend_embedding (g : BorelGroup) (S : Space) :
    extend g (cornerEmbedding S)=cornerEmbedding (act g.val S) := by
  change (positiveCornerHomeomorph (rootAction g (rootHomeomorph S))).val=
    (positiveCornerHomeomorph (rootHomeomorph (act g.val S))).val
  rw [rootHomeomorph_act]

@[simp] theorem extend_one (p : Corner) : extend 1 p=p := by
  have h : extend 1=id := cornerEmbedding_denseRange.equalizer
    (continuous_extend 1) continuous_id (by
      funext S
      simp only [Function.comp_apply,extend_embedding,OneMemClass.coe_one,act_one,id_eq])
  exact congrFun h p

theorem extend_mul (g h : BorelGroup) (p : Corner) : extend (g*h) p=extend g (extend h p) := by
  have he : extend (g*h)=extend g ∘ extend h := cornerEmbedding_denseRange.equalizer
    (continuous_extend (g*h)) ((continuous_extend g).comp (continuous_extend h)) (by
      funext S
      simp only [Function.comp_apply,extend_embedding,Subgroup.coe_mul,act_mul])
  exact congrFun he p

instance borelMulAction : MulAction BorelGroup Corner where
  smul := extend
  one_smul := extend_one
  mul_smul := extend_mul

instance borelContinuousSMul : ContinuousSMul BorelGroup Corner where
  continuous_smul := continuous_extend_joint

def extendedHomeomorph (g : BorelGroup) : Corner ≃ₜ Corner where
  toFun := extend g
  invFun := extend g⁻¹
  left_inv p := by rw [←extend_mul,inv_mul_cancel,extend_one]
  right_inv p := by rw [←extend_mul,mul_inv_cancel,extend_one]
  continuous_toFun := continuous_extend g
  continuous_invFun := continuous_extend g⁻¹

theorem extend_zero1_iff (g : BorelGroup) (p : Corner) :
    (extend g p).2.1.val=0 ↔ p.2.1.val=0 := by
  change factor1 g*p.2.1.val=0 ↔ _
  simp [ne_of_gt (factor1_pos g)]

theorem extend_zero2_iff (g : BorelGroup) (p : Corner) :
    (extend g p).2.2.val=0 ↔ p.2.2.val=0 := by
  change factor2 g*p.2.2.val=0 ↔ _
  simp [ne_of_gt (factor2_pos g)]

theorem extend_pos1_iff (g : BorelGroup) (p : Corner) :
    0<(extend g p).2.1.val ↔ 0<p.2.1.val :=
  mul_pos_iff_of_pos_left (factor1_pos g)

theorem extend_pos2_iff (g : BorelGroup) (p : Corner) :
    0<(extend g p).2.2.val ↔ 0<p.2.2.val :=
  mul_pos_iff_of_pos_left (factor2_pos g)

def planeFace : Set Corner := {p | p.2.2.val=0 ∧ 0<p.2.1.val}
def lineFace : Set Corner := {p | p.2.1.val=0 ∧ 0<p.2.2.val}
def fullFlagFace : Set Corner := {p | p.2.1.val=0 ∧ p.2.2.val=0}

theorem extend_interior_iff (g : BorelGroup) (p : Corner) :
    extend g p∈cornerInterior ↔ p∈cornerInterior := by
  exact and_congr (extend_pos1_iff g p) (extend_pos2_iff g p)

theorem extend_planeFace_iff (g : BorelGroup) (p : Corner) :
    extend g p∈planeFace ↔ p∈planeFace :=
  and_congr (extend_zero2_iff g p) (extend_pos1_iff g p)

theorem extend_lineFace_iff (g : BorelGroup) (p : Corner) :
    extend g p∈lineFace ↔ p∈lineFace :=
  and_congr (extend_zero1_iff g p) (extend_pos2_iff g p)

theorem extend_fullFlagFace_iff (g : BorelGroup) (p : Corner) :
    extend g p∈fullFlagFace ↔ p∈fullFlagFace :=
  and_congr (extend_zero1_iff g p) (extend_zero2_iff g p)

end TernaryPoly.SymmetricSpaceBorelCorner
