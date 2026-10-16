module

public import TernaryPeriodPolynomials.SymmetricSpace.Parabolic.CoordinatesScale
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceFlagCoordinates
open Matrix
open SymmetricSpaceParabolicCoordinates

/-- The exact binary upper-triangular LDL matrix. -/
def binaryLDL (x a b : ℝ) : Mat2 := !![a+x^2*b,x*b;x*b,b]

/-- Positive pivots give an actual positive-definite binary form. -/
theorem binaryLDL_positive (x a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (binaryLDL x a b).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro w hw
    have heq : star w ⬝ᵥ (binaryLDL x a b *ᵥ w)=a*(w 0)^2+b*(x*w 0+w 1)^2 := by
      simp [binaryLDL,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
      ring
    rw [heq]
    by_cases h0 : w 0=0
    · have h1 : w 1≠0 := by
        intro h1
        apply hw
        ext i
        fin_cases i <;> assumption
      simpa [h0] using mul_pos hb (sq_pos_of_ne_zero h1)
    · exact add_pos_of_pos_of_nonneg (mul_pos ha (sq_pos_of_ne_zero h0))
        (mul_nonneg hb.le (sq_nonneg _))

/-- The actual upper shear and two positive pivots of a binary form. -/
def binaryX (B : Mat2) : ℝ := B 0 1/B 1 1

def binaryA (B : Mat2) : ℝ := B 0 0-(B 0 1)^2/B 1 1

def binaryB (B : Mat2) : ℝ := B 1 1

theorem binaryB_pos (B : PosDef2) : 0<binaryB B.val := B.property.diag_pos

theorem binaryA_pos (B : PosDef2) : 0<binaryA B.val := by
  have hb : 0<B.val 1 1 := binaryB_pos B
  have hdet := B.property.det_pos
  have hs : B.val 1 0=B.val 0 1 :=
    (Matrix.isHermitian_iff_isSymm.mp B.property.isHermitian).apply 0 1
  have heq : binaryA B.val=B.val.det/B.val 1 1 := by
    simp only [binaryA,Matrix.det_fin_two,hs]
    field_simp [ne_of_gt hb]
  rw [heq]
  exact div_pos hdet hb

/-- The binary coordinates reconstruct every positive-definite form literally. -/
theorem binaryLDL_coordinates (B : PosDef2) :
    binaryLDL (binaryX B.val) (binaryA B.val) (binaryB B.val)=B.val := by
  have hb : B.val 1 1≠0 := ne_of_gt (binaryB_pos B)
  have hs : B.val 1 0=B.val 0 1 :=
    (Matrix.isHermitian_iff_isSymm.mp B.property.isHermitian).apply 0 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryLDL,binaryX,binaryA,binaryB,hs] <;> field_simp [hb]
  ring

@[simp] theorem binaryX_LDL (x a b : ℝ) (hb : b≠0) : binaryX (binaryLDL x a b)=x := by
  simp [binaryX,binaryLDL,hb]

@[simp] theorem binaryA_LDL (x a b : ℝ) : binaryA (binaryLDL x a b)=a := by
  simp [binaryA,binaryLDL]
  field_simp
  ring

@[simp] theorem binaryB_LDL (x a b : ℝ) : binaryB (binaryLDL x a b)=b := rfl

/-- The exact binary LDL parametrization as a homeomorphism. -/
def binaryLDLHomeomorph : PosDef2 ≃ₜ (ℝ × (PositiveScale × PositiveScale)) where
  toFun B := (binaryX B.val,(⟨binaryA B.val,binaryA_pos B⟩,⟨binaryB B.val,binaryB_pos B⟩))
  invFun p := ⟨binaryLDL p.1 p.2.1.val p.2.2.val,
    binaryLDL_positive _ _ _ p.2.1.property p.2.2.property⟩
  left_inv B := by apply Subtype.ext; exact binaryLDL_coordinates B
  right_inv p := by
    apply Prod.ext
    · exact binaryX_LDL _ _ _ (ne_of_gt p.2.2.property)
    · apply Prod.ext
      · apply Subtype.ext; exact binaryA_LDL _ _ _
      · apply Subtype.ext; rfl
  continuous_toFun := by
    have hentry (i j : Fin 2) : Continuous (fun B : PosDef2 => B.val i j) :=
      continuous_subtype_val.matrix_elem i j
    have hden (B : PosDef2) : B.val 1 1≠0 := ne_of_gt (binaryB_pos B)
    refine Continuous.prodMk ((hentry 0 1).div₀ (hentry 1 1) hden) ?_
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact (hentry 0 0).sub (((hentry 0 1).pow 2).div₀ (hentry 1 1) hden)
    · exact Continuous.subtype_mk (hentry 1 1) _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;> dsimp [binaryLDL]
    all_goals fun_prop

end TernaryPoly.SymmetricSpaceFlagCoordinates
