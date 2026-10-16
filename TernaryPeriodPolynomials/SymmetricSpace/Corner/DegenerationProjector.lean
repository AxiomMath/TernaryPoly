module

public import TernaryPeriodPolynomials.SymmetricSpace.Corner.DegenerationDual
public import TernaryPeriodPolynomials.SymmetricSpace.Borel.CornerGroup

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceCornerDegeneration
open Matrix SymmetricSpacePositive SymmetricSpaceLineBordification SymmetricSpaceBorelCorner

def basisProjector (j : Fin 3) : Mat := Matrix.diagonal (Pi.single j 1)

@[simp] theorem basisProjector_trace (j : Fin 3) : (basisProjector j).trace=1 := by
  simp [basisProjector,Matrix.trace]

theorem basisProjector_ne_zero (j : Fin 3) : basisProjector j≠0 := by
  intro h
  have he := basisProjector_trace j
  rw [h,Matrix.trace_zero] at he
  exact zero_ne_one he

theorem basisProjector_psd (j : Fin 3) : (basisProjector j).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  simp only [Pi.single_apply]
  split <;> norm_num

theorem basisProjector_diag_of_ne (i j : Fin 3) (h : i≠j) : basisProjector j i i=0 := by
  simp [basisProjector,h]

theorem conjugate_projector_diag (g : RealGL) (i j : Fin 3) :
    conjugate g (basisProjector j) i i=(g.val i j)^2 := by
  fin_cases j <;>
    simp [conjugate,basisProjector,Matrix.mul_apply,Fin.sum_univ_succ,pow_two]

/-- Equality of a normalized rank-one positive ray forces the actual image column to remain on
that same coordinate line. -/
theorem normalized_projector_fixed_column (g : RealGL) (j : Fin 3)
    (hfix : SymmetricSpacePositive.normalize (conjugate g (basisProjector j))=basisProjector j)
    (i : Fin 3) (hij : i≠j) : g.val i j=0 := by
  have ht := conjugate_trace_pos g (basisProjector_psd j) (basisProjector_ne_zero j)
  have h := congrArg (fun M : Mat => M i i) hfix
  change (conjugate g (basisProjector j)).trace⁻¹*conjugate g (basisProjector j) i i=
    basisProjector j i i at h
  rw [conjugate_projector_diag,basisProjector_diag_of_ne i j hij] at h
  have hs := (mul_eq_zero.mp h).resolve_left (inv_ne_zero (ne_of_gt ht))
  exact sq_eq_zero_iff.mp hs

theorem E00_eq_projector : E00=basisProjector 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E00,basisProjector]

theorem E22_eq_projector : E22=basisProjector 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E22,basisProjector]

theorem fixed_E00_line (g : RealGL)
    (h : SymmetricSpacePositive.normalize (conjugate g E00)=E00) :
    g.val 1 0=0 ∧ g.val 2 0=0 := by
  rw [E00_eq_projector] at h
  exact ⟨normalized_projector_fixed_column g 0 h 1 (by decide),
    normalized_projector_fixed_column g 0 h 2 (by decide)⟩

/-- A fixed dual e2-ray means the original real matrix preserves the actual e0,e1-plane. -/
theorem fixed_dual_E22_plane (g : RealGL)
    (h : SymmetricSpacePositive.normalize (conjugate (contragredient g) E22)=E22) :
    g.val 2 0=0 ∧ g.val 2 1=0 := by
  rw [E22_eq_projector] at h
  have h0 := normalized_projector_fixed_column (contragredient g) 2 h 0 (by decide)
  have h1 := normalized_projector_fixed_column (contragredient g) 2 h 1 (by decide)
  have hi : g⁻¹∈planeStabilizer := by
    apply (mem_planeStabilizer_iff _).mpr
    constructor
    · simpa only [contragredient,Units.coe_star,Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply,star_trivial] using h0
    · simpa only [contragredient,Units.coe_star,Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply,star_trivial] using h1
  apply (mem_planeStabilizer_iff g).mp
  simpa only [inv_inv] using planeStabilizer.inv_mem hi

end TernaryPoly.SymmetricSpaceCornerDegeneration
