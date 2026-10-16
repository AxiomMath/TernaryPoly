module

public import TernaryPeriodPolynomials.SymmetricSpace.Line.BordificationGroupTopology

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBorelCorner
open Matrix
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates
open SymmetricSpacePlaneBordification SymmetricSpaceLineBordification

/-- The actual real stabilizer of the standard e0,e1-plane. -/
def planeStabilizer : Subgroup RealGL := toRealGLHom.range
abbrev PlaneGroup := planeStabilizer

theorem mem_planeStabilizer_iff (g : RealGL) :
    g∈planeStabilizer ↔ g.val 2 0=0 ∧ g.val 2 1=0 := by
  constructor
  · rintro ⟨p,rfl⟩; exact ⟨rfl,rfl⟩
  · rintro ⟨h0,h1⟩; exact exists_plane_parameters g h0 h1

/-- The full standard real Borel is literally the intersection of the two actual parabolics. -/
def borelStabilizer : Subgroup RealGL := planeStabilizer ⊓ lineStabilizer
abbrev BorelGroup := borelStabilizer

theorem borel_eq_intersection : borelStabilizer=planeStabilizer ⊓ lineStabilizer := rfl

theorem mem_borelStabilizer_iff (g : RealGL) :
    g∈borelStabilizer ↔ g.val 1 0=0 ∧ g.val 2 0=0 ∧ g.val 2 1=0 := by
  change (g∈planeStabilizer ∧ g∈lineStabilizer) ↔ _
  rw [mem_planeStabilizer_iff,mem_lineStabilizer_iff]
  tauto

/-- Literal signed upper-triangular entries, in the order a,b,c,d,e,f. -/
def upperMatrix (a b c d e f : ℝ) : Mat := !![a,b,c;0,d,e;0,0,f]

theorem upperMatrix_det (a b c d e f : ℝ) : (upperMatrix a b c d e f).det=a*d*f := by
  simp [upperMatrix,Matrix.det_fin_three]

def signedUpper (a b c d e f : ℝ) (ha : a≠0) (hd : d≠0) (hf : f≠0) : BorelGroup :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (upperMatrix a b c d e f)
    (by rw [upperMatrix_det]; exact mul_ne_zero (mul_ne_zero ha hd) hf),
    (mem_borelStabilizer_iff _).mpr ⟨rfl,rfl,rfl⟩⟩

@[simp] theorem signedUpper_val (a b c d e f : ℝ) (ha : a≠0) (hd : d≠0) (hf : f≠0) :
    (signedUpper a b c d e f ha hd hf).val.val=upperMatrix a b c d e f := rfl

theorem matrix_eq_upper (g : BorelGroup) :
    g.val.val=upperMatrix (g.val.val 0 0) (g.val.val 0 1) (g.val.val 0 2)
      (g.val.val 1 1) (g.val.val 1 2) (g.val.val 2 2) := by
  obtain ⟨h10,h20,h21⟩ := (mem_borelStabilizer_iff g.val).mp g.property
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperMatrix,h10,h20,h21]

theorem diagonal_nonzero (g : BorelGroup) :
    g.val.val 0 0≠0 ∧ g.val.val 1 1≠0 ∧ g.val.val 2 2≠0 := by
  have h := g.val.det_ne_zero
  rw [matrix_eq_upper,upperMatrix_det] at h
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).2,(mul_ne_zero_iff.mp h).2⟩

def factor1 (g : BorelGroup) : ℝ := |g.val.val 1 1/g.val.val 0 0|
def factor2 (g : BorelGroup) : ℝ := |g.val.val 2 2/g.val.val 1 1|

theorem factor1_pos (g : BorelGroup) : 0<factor1 g :=
  abs_pos.mpr (div_ne_zero (diagonal_nonzero g).2.1 (diagonal_nonzero g).1)

theorem factor2_pos (g : BorelGroup) : 0<factor2 g :=
  abs_pos.mpr (div_ne_zero (diagonal_nonzero g).2.2 (diagonal_nonzero g).2.1)

theorem continuous_entry (i j : Fin 3) : Continuous (fun g : BorelGroup => g.val.val i j) :=
  (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j

theorem continuous_factor1 : Continuous factor1 :=
  ((continuous_entry 1 1).div₀ (continuous_entry 0 0) (fun g => (diagonal_nonzero g).1)).abs

theorem continuous_factor2 : Continuous factor2 :=
  ((continuous_entry 2 2).div₀ (continuous_entry 1 1) (fun g => (diagonal_nonzero g).2.1)).abs

end TernaryPoly.SymmetricSpaceBorelCorner
