module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.SquaredCoefficients
public import Mathlib.Algebra.CharP.Two

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoOrbitFrames
open CharTwoNorm

abbrev x : Poly := X 0
abbrev y : Poly := X 1
abbrev z : Poly := X 2

private theorem ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly) = ((n % 2 : ℕ) : Poly) := CharP.cast_eq_mod Poly 2 n

def frame_0 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, y, z]

theorem frame_0_d4 : frame_0 d4 = d4 := by
  simp [frame_0,d4,a,b,c,x,y,z]

theorem frame_0_d6 : frame_0 d6 = d6 := by
  simp [frame_0,d6,a,b,c,x,y,z]

theorem frame_0_d7 : frame_0 d7 = d7 := by
  simp [frame_0,d7,a,b,c,cplus,x,y,z]

def frame_1 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, y, x+z]

theorem frame_1_d4 : frame_1 d4 = d4 := by
  simp [frame_1,d4,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_1_d6 : frame_1 d6 = d6 := by
  simp [frame_1,d6,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_1_d7 : frame_1 d7 = d7 := by
  simp [frame_1,d7,a,b,c,cplus,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def frame_2 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, y, y+z]

theorem frame_2_d4 : frame_2 d4 = d4 := by
  simp [frame_2,d4,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_2_d6 : frame_2 d6 = d6 := by
  simp [frame_2,d6,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_2_d7 : frame_2 d7 = d7 := by
  simp [frame_2,d7,a,b,c,cplus,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def frame_3 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, y, x+y+z]

theorem frame_3_d4 : frame_3 d4 = d4 := by
  simp [frame_3,d4,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_3_d6 : frame_3 d6 = d6 := by
  simp [frame_3,d6,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_3_d7 : frame_3 d7 = d7 := by
  simp [frame_3,d7,a,b,c,cplus,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def frame_4 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, x+y, z]

theorem frame_4_d4 : frame_4 d4 = d4 := by
  simp [frame_4,d4,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_4_d6 : frame_4 d6 = d6 := by
  simp [frame_4,d6,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_4_d7 : frame_4 d7 = d7 := by
  simp [frame_4,d7,a,b,c,cplus,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def frame_5 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, x+y, x+z]

theorem frame_5_d4 : frame_5 d4 = d4 := by
  simp [frame_5,d4,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_5_d6 : frame_5 d6 = d6 := by
  simp [frame_5,d6,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_5_d7 : frame_5 d7 = d7 := by
  simp [frame_5,d7,a,b,c,cplus,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def frame_6 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, x+y, y+z]

theorem frame_6_d4 : frame_6 d4 = d4 := by
  simp [frame_6,d4,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_6_d6 : frame_6 d6 = d6 := by
  simp [frame_6,d6,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_6_d7 : frame_6 d7 = d7 := by
  simp [frame_6,d7,a,b,c,cplus,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def frame_7 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, x+y, x+y+z]

theorem frame_7_d4 : frame_7 d4 = d4 := by
  simp [frame_7,d4,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_7_d6 : frame_7 d6 = d6 := by
  simp [frame_7,d6,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_7_d7 : frame_7 d7 = d7 := by
  simp [frame_7,d7,a,b,c,cplus,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def frame_8 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, z, y]

theorem frame_8_d4 : frame_8 d4 = d4 := by
  simp [frame_8,d4,a,b,c,x,y,z]
  ring_nf

theorem frame_8_d6 : frame_8 d6 = d6 := by
  simp [frame_8,d6,a,b,c,x,y,z]
  ring_nf

theorem frame_8_d7 : frame_8 d7 = d7 := by
  simp [frame_8,d7,a,b,c,cplus,x,y,z]
  ring_nf

def frame_9 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, z, x+y]

theorem frame_9_d4 : frame_9 d4 = d4 := by
  simp [frame_9,d4,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_9_d6 : frame_9 d6 = d6 := by
  simp [frame_9,d6,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_9_d7 : frame_9 d7 = d7 := by
  simp [frame_9,d7,a,b,c,cplus,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def frame_10 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, x+z, y]

theorem frame_10_d4 : frame_10 d4 = d4 := by
  simp [frame_10,d4,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_10_d6 : frame_10 d6 = d6 := by
  simp [frame_10,d6,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_10_d7 : frame_10 d7 = d7 := by
  simp [frame_10,d7,a,b,c,cplus,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def frame_11 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, x+z, x+y]

theorem frame_11_d4 : frame_11 d4 = d4 := by
  simp [frame_11,d4,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_11_d6 : frame_11 d6 = d6 := by
  simp [frame_11,d6,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_11_d7 : frame_11 d7 = d7 := by
  simp [frame_11,d7,a,b,c,cplus,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def frame_12 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, y+z, y]

theorem frame_12_d4 : frame_12 d4 = d4 := by
  simp [frame_12,d4,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_12_d6 : frame_12 d6 = d6 := by
  simp [frame_12,d6,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_12_d7 : frame_12 d7 = d7 := by
  simp [frame_12,d7,a,b,c,cplus,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def frame_13 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, y+z, x+y]

theorem frame_13_d4 : frame_13 d4 = d4 := by
  simp [frame_13,d4,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_13_d6 : frame_13 d6 = d6 := by
  simp [frame_13,d6,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_13_d7 : frame_13 d7 = d7 := by
  simp [frame_13,d7,a,b,c,cplus,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def frame_14 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, x+y+z, y]

theorem frame_14_d4 : frame_14 d4 = d4 := by
  simp [frame_14,d4,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_14_d6 : frame_14 d6 = d6 := by
  simp [frame_14,d6,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_14_d7 : frame_14 d7 = d7 := by
  simp [frame_14,d7,a,b,c,cplus,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def frame_15 : Poly →ₐ[ZMod 2] Poly := bind₁ ![x, x+y+z, x+y]

theorem frame_15_d4 : frame_15 d4 = d4 := by
  simp [frame_15,d4,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_15_d6 : frame_15 d6 = d6 := by
  simp [frame_15,d6,a,b,c,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem frame_15_d7 : frame_15 d7 = d7 := by
  simp [frame_15,d7,a,b,c,cplus,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def frame : Fin 16 → Poly →ₐ[ZMod 2] Poly := ![frame_0, frame_1, frame_2, frame_3, frame_4, frame_5, frame_6, frame_7, frame_8, frame_9, frame_10, frame_11, frame_12, frame_13, frame_14, frame_15]

theorem frame_d4 (i : Fin 16) : frame i d4 = d4 := by
  fin_cases i
  · exact frame_0_d4
  · exact frame_1_d4
  · exact frame_2_d4
  · exact frame_3_d4
  · exact frame_4_d4
  · exact frame_5_d4
  · exact frame_6_d4
  · exact frame_7_d4
  · exact frame_8_d4
  · exact frame_9_d4
  · exact frame_10_d4
  · exact frame_11_d4
  · exact frame_12_d4
  · exact frame_13_d4
  · exact frame_14_d4
  · exact frame_15_d4

theorem frame_d6 (i : Fin 16) : frame i d6 = d6 := by
  fin_cases i
  · exact frame_0_d6
  · exact frame_1_d6
  · exact frame_2_d6
  · exact frame_3_d6
  · exact frame_4_d6
  · exact frame_5_d6
  · exact frame_6_d6
  · exact frame_7_d6
  · exact frame_8_d6
  · exact frame_9_d6
  · exact frame_10_d6
  · exact frame_11_d6
  · exact frame_12_d6
  · exact frame_13_d6
  · exact frame_14_d6
  · exact frame_15_d6

theorem frame_d7 (i : Fin 16) : frame i d7 = d7 := by
  fin_cases i
  · exact frame_0_d7
  · exact frame_1_d7
  · exact frame_2_d7
  · exact frame_3_d7
  · exact frame_4_d7
  · exact frame_5_d7
  · exact frame_6_d7
  · exact frame_7_d7
  · exact frame_8_d7
  · exact frame_9_d7
  · exact frame_10_d7
  · exact frame_11_d7
  · exact frame_12_d7
  · exact frame_13_d7
  · exact frame_14_d7
  · exact frame_15_d7

theorem frame_squaredInvariantEval (i : Fin 16) (q : Poly) :
    frame i (squaredInvariantEval q) = squaredInvariantEval q := by
  have he : (frame i).comp squaredInvariantEval = squaredInvariantEval := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;> simp [squaredInvariantEval,frame_d4,frame_d6,frame_d7]
  exact DFunLike.congr_fun he q

end TernaryPoly.CharTwoOrbitFrames
