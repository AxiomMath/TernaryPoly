module

public import TernaryPeriodPolynomials.SymmetricSpace.Line.BordificationPermutation
public import TernaryPeriodPolynomials.SymmetricSpace.Plane.BordificationParameterTopology
public import Mathlib.Algebra.Group.Subgroup.Ker

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceLineBordification
open Matrix
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates
open SymmetricSpacePlaneBordification

def topBlock (g : RealGL) : Mat2 := !![g.val 0 0,g.val 0 1;g.val 1 0,g.val 1 1]
def topVector (g : RealGL) : Vec2 := ![g.val 0 2,g.val 1 2]

theorem block_of_zero_row (g : RealGL) (h0 : g.val 2 0=0) (h1 : g.val 2 1=0) :
    blockMatrix (topBlock g) (topVector g) (g.val 2 2)=g.val := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMatrix,topBlock,topVector,h0,h1]

/-- Every actual invertible plane-preserving matrix has the complete signed block parameters. -/
theorem exists_plane_parameters (g : RealGL) (h0 : g.val 2 0=0) (h1 : g.val 2 1=0) :
    ∃ p : Parameters, toRealGL p=g := by
  have hdet : (topBlock g).det*g.val 2 2≠0 := by
    rw [←blockMatrix_det,block_of_zero_row g h0 h1]
    exact g.det_ne_zero
  have ha := (mul_ne_zero_iff.mp hdet).1
  have hd := (mul_ne_zero_iff.mp hdet).2
  refine ⟨⟨GeneralLinearGroup.mkOfDetNeZero (topBlock g) ha,topVector g,Units.mk0 (g.val 2 2) hd⟩,?_⟩
  apply Units.ext
  exact block_of_zero_row g h0 h1

/-- Signed plane parameters act on the genuine e0-line through the dual group involution. -/
def toLineGLHom : Parameters →* RealGL := dualGLEquiv.toMonoidHom.comp toRealGLHom

def toLineGL (p : Parameters) : RealGL := toLineGLHom p

theorem toLineGL_injective : Function.Injective toLineGL :=
  dualGLEquiv.injective.comp toRealGL_injective

@[simp] theorem dualGL_toLineGL (p : Parameters) : dualGL (toLineGL p)=toRealGL p :=
  dualGL_involutive _

theorem toLineGL_zero_col (p : Parameters) :
    (toLineGL p).val 1 0=0 ∧ (toLineGL p).val 2 0=0 := by
  have he : toLineGL p=flipGL*star (toRealGL p⁻¹)*flipGL := by
    rw [toRealGL_inv]
    rfl
  rw [he]
  change (flipMatrix*star (blockMatrix (p⁻¹).A.val (p⁻¹).u (p⁻¹).d.val)*flipMatrix) 1 0=0 ∧
    (flipMatrix*star (blockMatrix (p⁻¹).A.val (p⁻¹).u (p⁻¹).d.val)*flipMatrix) 2 0=0
  simp [flipMatrix,blockMatrix,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.star_eq_conjTranspose,Matrix.vecMul,dotProduct]

/-- The image consists of all and only the actual matrices preserving the standard e0-line. -/
theorem exists_line_parameters_iff (g : RealGL) :
    (∃ p : Parameters,toLineGL p=g) ↔ g.val 1 0=0 ∧ g.val 2 0=0 := by
  constructor
  · rintro ⟨p,rfl⟩; exact toLineGL_zero_col p
  · rintro ⟨h10,h20⟩
    have he : dualGL g⁻¹=flipGL*star g*flipGL := by simp [dualGL,contragredient]
    have h0 : (dualGL g⁻¹).val 2 0=0 := by
      rw [he]
      change (flipMatrix*star g.val*flipMatrix) 2 0=0
      simpa [flipMatrix,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.star_eq_conjTranspose,Matrix.vecMul,dotProduct] using h20
    have h1 : (dualGL g⁻¹).val 2 1=0 := by
      rw [he]
      change (flipMatrix*star g.val*flipMatrix) 2 1=0
      simpa [flipMatrix,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.star_eq_conjTranspose,Matrix.vecMul,dotProduct] using h10
    obtain ⟨p,hp⟩ := exists_plane_parameters (dualGL g⁻¹) h0 h1
    refine ⟨p⁻¹,?_⟩
    change dualGLEquiv (toRealGL p⁻¹)=g
    rw [toRealGL_inv,hp]
    change dualGLEquiv ((dualGLEquiv g⁻¹)⁻¹)=g
    rw [←map_inv,inv_inv]
    exact dualGL_involutive g

/-- The literal real subgroup stabilizing the line spanned by e0. -/
def lineStabilizer : Subgroup RealGL := toLineGLHom.range
abbrev LineGroup := lineStabilizer

@[simp] theorem mem_lineStabilizer_iff (g : RealGL) :
    g∈lineStabilizer ↔ g.val 1 0=0 ∧ g.val 2 0=0 := exists_line_parameters_iff g

/-- A faithful and exhaustive group parametrization, with both independent determinant signs retained. -/
def lineParametersEquiv : Parameters ≃* LineGroup :=
  MonoidHom.ofInjective (show Function.Injective toLineGLHom from toLineGL_injective)

@[simp] theorem lineParametersEquiv_val (p : Parameters) :
    (lineParametersEquiv p).val=toLineGL p := rfl

@[simp] theorem lineParametersEquiv_symm_matrix (g : LineGroup) :
    toRealGL (lineParametersEquiv.symm g)=dualGL g.val := by
  have h := congrArg Subtype.val (lineParametersEquiv.apply_symm_apply g)
  have hd := congrArg dualGL h
  simpa only [lineParametersEquiv_val,dualGL_toLineGL] using hd

/-- Literal action on the standard basis vector spanning the line. -/
theorem lineGroup_e0 (g : LineGroup) :
    g.val.val *ᵥ (![1,0,0] : Fin 3 → ℝ)=g.val.val 0 0 • (![1,0,0] : Fin 3 → ℝ) := by
  obtain ⟨h10,h20⟩ := (mem_lineStabilizer_iff g.val).mp g.property
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,h10,h20]

theorem lineGroup_leading_ne_zero (g : LineGroup) : g.val.val 0 0≠0 := by
  obtain ⟨h10,h20⟩ := (mem_lineStabilizer_iff g.val).mp g.property
  intro h00
  apply g.val.det_ne_zero
  simp [Matrix.det_fin_three,h00,h10,h20]

/-- The group involution exchanges exactly the e0-line and e0,e1-plane stabilizers. -/
theorem dualGL_plane_iff_line (g : RealGL) :
    (dualGL g).val 2 0=0 ∧ (dualGL g).val 2 1=0 ↔ g∈lineStabilizer := by
  constructor
  · rintro ⟨h0,h1⟩
    obtain ⟨p,hp⟩ := exists_plane_parameters (dualGL g) h0 h1
    refine ⟨p,?_⟩
    change dualGL (toRealGL p)=g
    rw [hp,dualGL_involutive]
  · intro hg
    obtain ⟨p,rfl⟩ := hg
    change (dualGL (toLineGL p)).val 2 0=0 ∧ (dualGL (toLineGL p)).val 2 1=0
    rw [dualGL_toLineGL]
    exact ⟨rfl,rfl⟩

end TernaryPoly.SymmetricSpaceLineBordification
