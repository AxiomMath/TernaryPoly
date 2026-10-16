module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.FormalSource
public import TernaryPeriodPolynomials.Polynomial.CharTwo.CartierFormula

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoSymbolRows
open CharTwoToddSymbol

private theorem ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly) = ((n % 2 : ℕ) : Poly) := CharP.cast_eq_mod Poly 2 n

def component_0_0 : Poly := z
def component_0_1 : Poly := 0
def component_0_2 : Poly := 0
def component_0_3 : Poly := 1

theorem source_cartier_0 : CharTwoFormal.source32 (0,0,0) = cartierInput (component_0_0) (component_0_1) (component_0_2) (component_0_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_0_0,component_0_1,component_0_2,component_0_3]
  ring_nf

def row_0_0 : Poly := x*y*z^5 + x*y^3*z^3 + x^2*y*z^4 + x^2*y^3*z^2

theorem root_row_0_0 : cartierP (component_0_1) (component_0_2) (component_0_3) = row_0_0 := by
  simp [cartierP,component_0_1,component_0_2,component_0_3,row_0_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_0_0 : symbolP (CharTwoFormal.source32 (0,0,0)) = row_0_0^2 := by
  rw [source_cartier_0,symbolP_cartierInput,root_row_0_0]

def row_0_1 : Poly := y^2*z^5 + y^3*z^4 + y^4*z^3 + y^5*z^2 + x*y^3*z^3 + x*y^5*z + x^2*y^2*z^3 + x^2*y^4*z

theorem root_row_0_1 : cartierQ (component_0_1) (component_0_2) (component_0_3) = row_0_1 := by
  simp [cartierQ,component_0_1,component_0_2,component_0_3,row_0_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_0_1 : symbolQ (CharTwoFormal.source32 (0,0,0)) = row_0_1^2 := by
  rw [source_cartier_0,symbolQ_cartierInput,root_row_0_1]

def component_1_0 : Poly := z^2
def component_1_1 : Poly := x^2*z
def component_1_2 : Poly := x*z
def component_1_3 : Poly := x*y

theorem source_cartier_1 : CharTwoFormal.source32 (0,0,1) = cartierInput (component_1_0) (component_1_1) (component_1_2) (component_1_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_1_0,component_1_1,component_1_2,component_1_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_1_0 : Poly := x*y^2*z^7 + x*y^3*z^6 + x*y^4*z^5 + x*y^5*z^4 + x^2*y^2*z^6 + x^2*y^3*z^5 + x^2*y^4*z^4 + x^2*y^5*z^3

theorem root_row_1_0 : cartierP (component_1_1) (component_1_2) (component_1_3) = row_1_0 := by
  simp [cartierP,component_1_1,component_1_2,component_1_3,row_1_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_1_0 : symbolP (CharTwoFormal.source32 (0,0,1)) = row_1_0^2 := by
  rw [source_cartier_1,symbolP_cartierInput,root_row_1_0]

def row_1_1 : Poly := y^3*z^7 + y^7*z^3 + x*y^4*z^5 + x*y^5*z^4 + x*y^6*z^3 + x*y^7*z^2 + x^2*y^3*z^5 + x^2*y^4*z^4 + x^2*y^5*z^3 + x^2*y^6*z^2

theorem root_row_1_1 : cartierQ (component_1_1) (component_1_2) (component_1_3) = row_1_1 := by
  simp [cartierQ,component_1_1,component_1_2,component_1_3,row_1_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_1_1 : symbolQ (CharTwoFormal.source32 (0,0,1)) = row_1_1^2 := by
  rw [source_cartier_1,symbolQ_cartierInput,root_row_1_1]

def component_2_0 : Poly := y*z + x^2*z
def component_2_1 : Poly := x*z
def component_2_2 : Poly := z
def component_2_3 : Poly := y + x^2

theorem source_cartier_2 : CharTwoFormal.source32 (0,1,0) = cartierInput (component_2_0) (component_2_1) (component_2_2) (component_2_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_2_0,component_2_1,component_2_2,component_2_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_2_0 : Poly := x*y*z^7 + x*y^2*z^6 + x*y^4*z^4 + x*y^5*z^3 + x^2*y*z^6 + x^2*y^2*z^5 + x^2*y^4*z^3 + x^2*y^5*z^2

theorem root_row_2_0 : cartierP (component_2_1) (component_2_2) (component_2_3) = row_2_0 := by
  simp [cartierP,component_2_1,component_2_2,component_2_3,row_2_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_2_0 : symbolP (CharTwoFormal.source32 (0,1,0)) = row_2_0^2 := by
  rw [source_cartier_2,symbolP_cartierInput,root_row_2_0]

def row_2_1 : Poly := y^2*z^7 + y^4*z^5 + y^5*z^4 + y^7*z^2 + x*y^3*z^5 + x*y^4*z^4 + x*y^6*z^2 + x*y^7*z + x^2*y^2*z^5 + x^2*y^3*z^4 + x^2*y^5*z^2 + x^2*y^6*z

theorem root_row_2_1 : cartierQ (component_2_1) (component_2_2) (component_2_3) = row_2_1 := by
  simp [cartierQ,component_2_1,component_2_2,component_2_3,row_2_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_2_1 : symbolQ (CharTwoFormal.source32 (0,1,0)) = row_2_1^2 := by
  rw [source_cartier_2,symbolQ_cartierInput,root_row_2_1]

def component_3_0 : Poly := y*z^2
def component_3_1 : Poly := x^4*z
def component_3_2 : Poly := z^2 + x*y*z + x^3*z
def component_3_3 : Poly := x*y^2 + x^2*z + x^3*y

theorem source_cartier_3 : CharTwoFormal.source32 (0,1,1) = cartierInput (component_3_0) (component_3_1) (component_3_2) (component_3_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_3_0,component_3_1,component_3_2,component_3_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_3_0 : Poly := x*y^2*z^9 + x*y^3*z^8 + x*y^4*z^7 + x*y^5*z^6 + x^2*y^2*z^8 + x^2*y^4*z^6 + x^2*y^5*z^5 + x^2*y^7*z^3 + x^3*y*z^8 + x^3*y^2*z^7 + x^3*y^3*z^6 + x^3*y^4*z^5 + x^3*y^5*z^4 + x^3*y^7*z^2 + x^4*y*z^7 + x^4*y^3*z^5 + x^5*y*z^6 + x^5*y^2*z^5 + x^5*y^4*z^3 + x^5*y^5*z^2 + x^6*y*z^5 + x^6*y^3*z^3

theorem root_row_3_0 : cartierP (component_3_1) (component_3_2) (component_3_3) = row_3_0 := by
  simp [cartierP,component_3_1,component_3_2,component_3_3,row_3_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_3_0 : symbolP (CharTwoFormal.source32 (0,1,1)) = row_3_0^2 := by
  rw [source_cartier_3,symbolP_cartierInput,root_row_3_0]

def row_3_1 : Poly := y^3*z^9 + y^4*z^8 + y^5*z^7 + y^7*z^5 + y^8*z^4 + y^9*z^3 + x*y^3*z^8 + x*y^6*z^5 + x*y^8*z^3 + x*y^9*z^2 + x^2*y^2*z^8 + x^2*y^3*z^7 + x^2*y^4*z^6 + x^2*y^6*z^4 + x^2*y^7*z^3 + x^2*y^8*z^2 + x^3*y^2*z^7 + x^3*y^4*z^5 + x^3*y^5*z^4 + x^3*y^6*z^3 + x^3*y^7*z^2 + x^3*y^8*z + x^4*y^2*z^6 + x^4*y^3*z^5 + x^4*y^4*z^4 + x^4*y^7*z + x^5*y^2*z^5 + x^5*y^3*z^4 + x^5*y^5*z^2 + x^5*y^6*z + x^6*y^3*z^3 + x^6*y^5*z

theorem root_row_3_1 : cartierQ (component_3_1) (component_3_2) (component_3_3) = row_3_1 := by
  simp [cartierQ,component_3_1,component_3_2,component_3_3,row_3_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_3_1 : symbolQ (CharTwoFormal.source32 (0,1,1)) = row_3_1^2 := by
  rw [source_cartier_3,symbolQ_cartierInput,root_row_3_1]

def component_4_0 : Poly := x*z
def component_4_1 : Poly := 0
def component_4_2 : Poly := 0
def component_4_3 : Poly := x

theorem source_cartier_4 : CharTwoFormal.source32 (1,0,0) = cartierInput (component_4_0) (component_4_1) (component_4_2) (component_4_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_4_0,component_4_1,component_4_2,component_4_3]
  ring_nf

def row_4_0 : Poly := x*y*z^6 + x*y^2*z^5 + x*y^3*z^4 + x*y^4*z^3 + x^2*y*z^5 + x^2*y^2*z^4 + x^2*y^3*z^3 + x^2*y^4*z^2

theorem root_row_4_0 : cartierP (component_4_1) (component_4_2) (component_4_3) = row_4_0 := by
  simp [cartierP,component_4_1,component_4_2,component_4_3,row_4_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_4_0 : symbolP (CharTwoFormal.source32 (1,0,0)) = row_4_0^2 := by
  rw [source_cartier_4,symbolP_cartierInput,root_row_4_0]

def row_4_1 : Poly := y^2*z^6 + y^6*z^2 + x*y^3*z^4 + x*y^4*z^3 + x*y^5*z^2 + x*y^6*z + x^2*y^2*z^4 + x^2*y^3*z^3 + x^2*y^4*z^2 + x^2*y^5*z

theorem root_row_4_1 : cartierQ (component_4_1) (component_4_2) (component_4_3) = row_4_1 := by
  simp [cartierQ,component_4_1,component_4_2,component_4_3,row_4_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_4_1 : symbolQ (CharTwoFormal.source32 (1,0,0)) = row_4_1^2 := by
  rw [source_cartier_4,symbolQ_cartierInput,root_row_4_1]

def component_5_0 : Poly := x*z^2
def component_5_1 : Poly := x^3*z
def component_5_2 : Poly := x^2*z
def component_5_3 : Poly := x^2*y

theorem source_cartier_5 : CharTwoFormal.source32 (1,0,1) = cartierInput (component_5_0) (component_5_1) (component_5_2) (component_5_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_5_0,component_5_1,component_5_2,component_5_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_5_0 : Poly := x*y^2*z^8 + x*y^6*z^4 + x^2*y^2*z^7 + x^2*y^6*z^3

theorem root_row_5_0 : cartierP (component_5_1) (component_5_2) (component_5_3) = row_5_0 := by
  simp [cartierP,component_5_1,component_5_2,component_5_3,row_5_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_5_0 : symbolP (CharTwoFormal.source32 (1,0,1)) = row_5_0^2 := by
  rw [source_cartier_5,symbolP_cartierInput,root_row_5_0]

def row_5_1 : Poly := y^3*z^8 + y^4*z^7 + y^7*z^4 + y^8*z^3 + x*y^4*z^6 + x*y^8*z^2 + x^2*y^3*z^6 + x^2*y^7*z^2

theorem root_row_5_1 : cartierQ (component_5_1) (component_5_2) (component_5_3) = row_5_1 := by
  simp [cartierQ,component_5_1,component_5_2,component_5_3,row_5_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_5_1 : symbolQ (CharTwoFormal.source32 (1,0,1)) = row_5_1^2 := by
  rw [source_cartier_5,symbolQ_cartierInput,root_row_5_1]

def component_6_0 : Poly := x*y*z + x^3*z
def component_6_1 : Poly := x^2*z
def component_6_2 : Poly := x*z
def component_6_3 : Poly := x*y + x^3

theorem source_cartier_6 : CharTwoFormal.source32 (1,1,0) = cartierInput (component_6_0) (component_6_1) (component_6_2) (component_6_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_6_0,component_6_1,component_6_2,component_6_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_6_0 : Poly := x*y*z^8 + x*y^3*z^6 + x*y^4*z^5 + x*y^6*z^3 + x^2*y*z^7 + x^2*y^3*z^5 + x^2*y^4*z^4 + x^2*y^6*z^2

theorem root_row_6_0 : cartierP (component_6_1) (component_6_2) (component_6_3) = row_6_0 := by
  simp [cartierP,component_6_1,component_6_2,component_6_3,row_6_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_6_0 : symbolP (CharTwoFormal.source32 (1,1,0)) = row_6_0^2 := by
  rw [source_cartier_6,symbolP_cartierInput,root_row_6_0]

def row_6_1 : Poly := y^2*z^8 + y^3*z^7 + y^4*z^6 + y^6*z^4 + y^7*z^3 + y^8*z^2 + x*y^3*z^6 + x*y^5*z^4 + x*y^6*z^3 + x*y^8*z + x^2*y^2*z^6 + x^2*y^4*z^4 + x^2*y^5*z^3 + x^2*y^7*z

theorem root_row_6_1 : cartierQ (component_6_1) (component_6_2) (component_6_3) = row_6_1 := by
  simp [cartierQ,component_6_1,component_6_2,component_6_3,row_6_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_6_1 : symbolQ (CharTwoFormal.source32 (1,1,0)) = row_6_1^2 := by
  rw [source_cartier_6,symbolQ_cartierInput,root_row_6_1]

def component_7_0 : Poly := x*y*z^2
def component_7_1 : Poly := x^5*z
def component_7_2 : Poly := x*z^2 + x^2*y*z + x^4*z
def component_7_3 : Poly := x^2*y^2 + x^3*z + x^4*y

theorem source_cartier_7 : CharTwoFormal.source32 (1,1,1) = cartierInput (component_7_0) (component_7_1) (component_7_2) (component_7_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_7_0,component_7_1,component_7_2,component_7_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_7_0 : Poly := x*y^2*z^10 + x*y^6*z^6 + x^2*y^2*z^9 + x^2*y^3*z^8 + x^2*y^4*z^7 + x^2*y^6*z^5 + x^2*y^7*z^4 + x^2*y^8*z^3 + x^3*y*z^9 + x^3*y^6*z^4 + x^3*y^7*z^3 + x^3*y^8*z^2 + x^4*y*z^8 + x^4*y^2*z^7 + x^4*y^3*z^6 + x^4*y^4*z^5 + x^5*y*z^7 + x^5*y^3*z^5 + x^5*y^4*z^4 + x^5*y^6*z^2 + x^6*y*z^6 + x^6*y^2*z^5 + x^6*y^3*z^4 + x^6*y^4*z^3

theorem root_row_7_0 : cartierP (component_7_1) (component_7_2) (component_7_3) = row_7_0 := by
  simp [cartierP,component_7_1,component_7_2,component_7_3,row_7_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_7_0 : symbolP (CharTwoFormal.source32 (1,1,1)) = row_7_0^2 := by
  rw [source_cartier_7,symbolP_cartierInput,root_row_7_0]

def row_7_1 : Poly := y^3*z^10 + y^6*z^7 + y^7*z^6 + y^10*z^3 + x*y^3*z^9 + x*y^4*z^8 + x*y^6*z^6 + x*y^7*z^5 + x*y^8*z^4 + x*y^10*z^2 + x^2*y^2*z^9 + x^2*y^5*z^6 + x^2*y^6*z^5 + x^2*y^9*z^2 + x^3*y^2*z^8 + x^3*y^3*z^7 + x^3*y^4*z^6 + x^3*y^9*z + x^4*y^2*z^7 + x^4*y^5*z^4 + x^4*y^7*z^2 + x^4*y^8*z + x^5*y^2*z^6 + x^5*y^4*z^4 + x^5*y^5*z^3 + x^5*y^7*z + x^6*y^3*z^4 + x^6*y^4*z^3 + x^6*y^5*z^2 + x^6*y^6*z

theorem root_row_7_1 : cartierQ (component_7_1) (component_7_2) (component_7_3) = row_7_1 := by
  simp [cartierQ,component_7_1,component_7_2,component_7_3,row_7_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_7_1 : symbolQ (CharTwoFormal.source32 (1,1,1)) = row_7_1^2 := by
  rw [source_cartier_7,symbolQ_cartierInput,root_row_7_1]

def component_8_0 : Poly := 0
def component_8_1 : Poly := x*z
def component_8_2 : Poly := z
def component_8_3 : Poly := 0

theorem source_cartier_8 : CharTwoFormal.source32 (2,0,0) = cartierInput (component_8_0) (component_8_1) (component_8_2) (component_8_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_8_0,component_8_1,component_8_2,component_8_3]
  ring_nf

def row_8_0 : Poly := x*y^2*z^6 + x*y^3*z^5 + x*y^4*z^4 + x*y^5*z^3 + x^2*y*z^6 + x^2*y^2*z^5 + x^2*y^4*z^3 + x^2*y^5*z^2 + x^4*y*z^4 + x^4*y^3*z^2

theorem root_row_8_0 : cartierP (component_8_1) (component_8_2) (component_8_3) = row_8_0 := by
  simp [cartierP,component_8_1,component_8_2,component_8_3,row_8_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_8_0 : symbolP (CharTwoFormal.source32 (2,0,0)) = row_8_0^2 := by
  rw [source_cartier_8,symbolP_cartierInput,root_row_8_0]

def row_8_1 : Poly := x*y^3*z^5 + x*y^4*z^4 + x*y^5*z^3 + x*y^6*z^2 + x^2*y^2*z^5 + x^2*y^3*z^4 + x^2*y^5*z^2 + x^2*y^6*z + x^4*y^2*z^3 + x^4*y^4*z

theorem root_row_8_1 : cartierQ (component_8_1) (component_8_2) (component_8_3) = row_8_1 := by
  simp [cartierQ,component_8_1,component_8_2,component_8_3,row_8_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_8_1 : symbolQ (CharTwoFormal.source32 (2,0,0)) = row_8_1^2 := by
  rw [source_cartier_8,symbolQ_cartierInput,root_row_8_1]

def component_9_0 : Poly := x^2*z^2
def component_9_1 : Poly := x^2*y*z
def component_9_2 : Poly := z^2
def component_9_3 : Poly := x^2*z

theorem source_cartier_9 : CharTwoFormal.source32 (2,0,1) = cartierInput (component_9_0) (component_9_1) (component_9_2) (component_9_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_9_0,component_9_1,component_9_2,component_9_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_9_0 : Poly := x^2*y^2*z^8 + x^2*y^4*z^6 + x^2*y^5*z^5 + x^2*y^7*z^3 + x^3*y*z^8 + x^3*y^2*z^7 + x^3*y^3*z^6 + x^3*y^4*z^5 + x^3*y^5*z^4 + x^3*y^7*z^2 + x^4*y*z^7 + x^4*y^2*z^6 + x^4*y^4*z^4 + x^4*y^5*z^3 + x^5*y*z^6 + x^5*y^2*z^5 + x^5*y^4*z^3 + x^5*y^5*z^2 + x^6*y*z^5 + x^6*y^3*z^3

theorem root_row_9_0 : cartierP (component_9_1) (component_9_2) (component_9_3) = row_9_0 := by
  simp [cartierP,component_9_1,component_9_2,component_9_3,row_9_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_9_0 : symbolP (CharTwoFormal.source32 (2,0,1)) = row_9_0^2 := by
  rw [source_cartier_9,symbolP_cartierInput,root_row_9_0]

def row_9_1 : Poly := x*y^3*z^8 + x*y^7*z^4 + x^2*y^2*z^8 + x^2*y^3*z^7 + x^2*y^4*z^6 + x^2*y^6*z^4 + x^2*y^7*z^3 + x^2*y^8*z^2 + x^3*y^2*z^7 + x^3*y^4*z^5 + x^3*y^5*z^4 + x^3*y^6*z^3 + x^3*y^7*z^2 + x^3*y^8*z + x^4*y^2*z^6 + x^4*y^5*z^3 + x^4*y^6*z^2 + x^4*y^7*z + x^5*y^2*z^5 + x^5*y^3*z^4 + x^5*y^5*z^2 + x^5*y^6*z + x^6*y^3*z^3 + x^6*y^5*z

theorem root_row_9_1 : cartierQ (component_9_1) (component_9_2) (component_9_3) = row_9_1 := by
  simp [cartierQ,component_9_1,component_9_2,component_9_3,row_9_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_9_1 : symbolQ (CharTwoFormal.source32 (2,0,1)) = row_9_1^2 := by
  rw [source_cartier_9,symbolQ_cartierInput,root_row_9_1]

def component_10_0 : Poly := x*z^2
def component_10_1 : Poly := x*y*z + x^3*z
def component_10_2 : Poly := y*z + x^2*z
def component_10_3 : Poly := x*z

theorem source_cartier_10 : CharTwoFormal.source32 (2,1,0) = cartierInput (component_10_0) (component_10_1) (component_10_2) (component_10_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_10_0,component_10_1,component_10_2,component_10_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_10_0 : Poly := x*y^2*z^8 + x*y^4*z^6 + x*y^5*z^5 + x*y^7*z^3 + x^2*y*z^8 + x^2*y^2*z^7 + x^2*y^3*z^6 + x^2*y^4*z^5 + x^2*y^5*z^4 + x^2*y^7*z^2 + x^3*y*z^7 + x^3*y^3*z^5 + x^5*y*z^5 + x^5*y^3*z^3 + x^6*y*z^4 + x^6*y^3*z^2

theorem root_row_10_0 : cartierP (component_10_1) (component_10_2) (component_10_3) = row_10_0 := by
  simp [cartierP,component_10_1,component_10_2,component_10_3,row_10_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_10_0 : symbolP (CharTwoFormal.source32 (2,1,0)) = row_10_0^2 := by
  rw [source_cartier_10,symbolP_cartierInput,root_row_10_0]

def row_10_1 : Poly := x*y^5*z^5 + x*y^6*z^4 + x*y^7*z^3 + x*y^8*z^2 + x^2*y^6*z^3 + x^2*y^8*z + x^3*y^5*z^3 + x^3*y^7*z + x^4*y^2*z^5 + x^4*y^3*z^4 + x^4*y^4*z^3 + x^4*y^5*z^2 + x^5*y^3*z^3 + x^5*y^5*z + x^6*y^2*z^3 + x^6*y^4*z

theorem root_row_10_1 : cartierQ (component_10_1) (component_10_2) (component_10_3) = row_10_1 := by
  simp [cartierQ,component_10_1,component_10_2,component_10_3,row_10_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_10_1 : symbolQ (CharTwoFormal.source32 (2,1,0)) = row_10_1^2 := by
  rw [source_cartier_10,symbolQ_cartierInput,root_row_10_1]

def component_11_0 : Poly := x*z^3 + x^2*y*z^2 + x^4*z^2
def component_11_1 : Poly := x^2*y^2*z + x^3*z^2 + x^4*y*z
def component_11_2 : Poly := y*z^2
def component_11_3 : Poly := x^4*z

theorem source_cartier_11 : CharTwoFormal.source32 (2,1,1) = cartierInput (component_11_0) (component_11_1) (component_11_2) (component_11_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_11_0,component_11_1,component_11_2,component_11_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_11_0 : Poly := x^2*y^2*z^10 + x^2*y^3*z^9 + x^2*y^8*z^4 + x^2*y^9*z^3 + x^3*y*z^10 + x^3*y^2*z^9 + x^3*y^8*z^3 + x^3*y^9*z^2 + x^4*y^2*z^8 + x^4*y^4*z^6 + x^4*y^5*z^5 + x^4*y^7*z^3 + x^5*y*z^8 + x^5*y^2*z^7 + x^5*y^3*z^6 + x^5*y^4*z^5 + x^5*y^5*z^4 + x^5*y^7*z^2 + x^6*y*z^7 + x^6*y^3*z^5 + x^8*y*z^5 + x^8*y^3*z^3

theorem root_row_11_0 : cartierP (component_11_1) (component_11_2) (component_11_3) = row_11_0 := by
  simp [cartierP,component_11_1,component_11_2,component_11_3,row_11_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_11_0 : symbolP (CharTwoFormal.source32 (2,1,1)) = row_11_0^2 := by
  rw [source_cartier_11,symbolP_cartierInput,root_row_11_0]

def row_11_1 : Poly := x*y^3*z^10 + x*y^7*z^6 + x^2*y^2*z^10 + x^2*y^3*z^9 + x^2*y^5*z^7 + x^2*y^7*z^5 + x^2*y^9*z^3 + x^2*y^10*z^2 + x^3*y^2*z^9 + x^3*y^3*z^8 + x^3*y^9*z^2 + x^3*y^10*z + x^4*y^2*z^8 + x^4*y^4*z^6 + x^4*y^6*z^4 + x^4*y^8*z^2 + x^5*y^2*z^7 + x^5*y^4*z^5 + x^5*y^5*z^4 + x^5*y^6*z^3 + x^5*y^7*z^2 + x^5*y^8*z + x^6*y^5*z^3 + x^6*y^7*z + x^8*y^3*z^3 + x^8*y^5*z

theorem root_row_11_1 : cartierQ (component_11_1) (component_11_2) (component_11_3) = row_11_1 := by
  simp [cartierQ,component_11_1,component_11_2,component_11_3,row_11_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_11_1 : symbolQ (CharTwoFormal.source32 (2,1,1)) = row_11_1^2 := by
  rw [source_cartier_11,symbolQ_cartierInput,root_row_11_1]

def component_12_0 : Poly := x*y*z
def component_12_1 : Poly := 0
def component_12_2 : Poly := 0
def component_12_3 : Poly := z

theorem source_cartier_12 : CharTwoFormal.source32 (3,0,0) = cartierInput (component_12_0) (component_12_1) (component_12_2) (component_12_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_12_0,component_12_1,component_12_2,component_12_3]
  ring_nf

def row_12_0 : Poly := x*y^3*z^6 + x*y^4*z^5 + x*y^5*z^4 + x*y^6*z^3 + x^2*y^2*z^6 + x^2*y^3*z^5 + x^2*y^5*z^3 + x^2*y^6*z^2 + x^4*y^2*z^4 + x^4*y^4*z^2

theorem root_row_12_0 : cartierP (component_12_1) (component_12_2) (component_12_3) = row_12_0 := by
  simp [cartierP,component_12_1,component_12_2,component_12_3,row_12_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_12_0 : symbolP (CharTwoFormal.source32 (3,0,0)) = row_12_0^2 := by
  rw [source_cartier_12,symbolP_cartierInput,root_row_12_0]

def row_12_1 : Poly := x*y^3*z^6 + x*y^4*z^5 + x*y^5*z^4 + x*y^6*z^3 + x^2*y^2*z^6 + x^2*y^3*z^5 + x^2*y^5*z^3 + x^2*y^6*z^2 + x^4*y^2*z^4 + x^4*y^4*z^2

theorem root_row_12_1 : cartierQ (component_12_1) (component_12_2) (component_12_3) = row_12_1 := by
  simp [cartierQ,component_12_1,component_12_2,component_12_3,row_12_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_12_1 : symbolQ (CharTwoFormal.source32 (3,0,0)) = row_12_1^2 := by
  rw [source_cartier_12,symbolQ_cartierInput,root_row_12_1]

def component_13_0 : Poly := x^2*y^2*z
def component_13_1 : Poly := x^2*z^2
def component_13_2 : Poly := x^2*y*z
def component_13_3 : Poly := z^2

theorem source_cartier_13 : CharTwoFormal.source32 (3,0,1) = cartierInput (component_13_0) (component_13_1) (component_13_2) (component_13_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_13_0,component_13_1,component_13_2,component_13_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_13_0 : Poly := x*y^3*z^9 + x*y^7*z^5 + x^2*y^2*z^9 + x^2*y^3*z^8 + x^2*y^4*z^7 + x^2*y^6*z^5 + x^2*y^7*z^4 + x^2*y^8*z^3 + x^3*y^2*z^8 + x^3*y^4*z^6 + x^3*y^5*z^5 + x^3*y^6*z^4 + x^3*y^7*z^3 + x^3*y^8*z^2 + x^4*y^2*z^7 + x^4*y^5*z^4 + x^4*y^6*z^3 + x^4*y^7*z^2 + x^5*y^2*z^6 + x^5*y^3*z^5 + x^5*y^5*z^3 + x^5*y^6*z^2 + x^6*y^3*z^4 + x^6*y^5*z^2

theorem root_row_13_0 : cartierP (component_13_1) (component_13_2) (component_13_3) = row_13_0 := by
  simp [cartierP,component_13_1,component_13_2,component_13_3,row_13_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_13_0 : symbolP (CharTwoFormal.source32 (3,0,1)) = row_13_0^2 := by
  rw [source_cartier_13,symbolP_cartierInput,root_row_13_0]

def row_13_1 : Poly := x^2*y^3*z^8 + x^2*y^5*z^6 + x^2*y^6*z^5 + x^2*y^8*z^3 + x^3*y^2*z^8 + x^3*y^3*z^7 + x^3*y^4*z^6 + x^3*y^5*z^5 + x^3*y^6*z^4 + x^3*y^8*z^2 + x^4*y^2*z^7 + x^4*y^3*z^6 + x^4*y^5*z^4 + x^4*y^6*z^3 + x^5*y^2*z^6 + x^5*y^3*z^5 + x^5*y^5*z^3 + x^5*y^6*z^2 + x^6*y^2*z^5 + x^6*y^4*z^3

theorem root_row_13_1 : cartierQ (component_13_1) (component_13_2) (component_13_3) = row_13_1 := by
  simp [cartierQ,component_13_1,component_13_2,component_13_3,row_13_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_13_1 : symbolQ (CharTwoFormal.source32 (3,0,1)) = row_13_1^2 := by
  rw [source_cartier_13,symbolQ_cartierInput,root_row_13_1]

def component_14_0 : Poly := x*y^2*z + x^3*y*z
def component_14_1 : Poly := x*z^2
def component_14_2 : Poly := x*y*z
def component_14_3 : Poly := y*z + x^2*z

theorem source_cartier_14 : CharTwoFormal.source32 (3,1,0) = cartierInput (component_14_0) (component_14_1) (component_14_2) (component_14_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_14_0,component_14_1,component_14_2,component_14_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_14_0 : Poly := x*y^5*z^6 + x*y^6*z^5 + x*y^7*z^4 + x*y^8*z^3 + x^2*y^6*z^4 + x^2*y^8*z^2 + x^3*y^5*z^4 + x^3*y^7*z^2 + x^4*y^2*z^6 + x^4*y^3*z^5 + x^4*y^4*z^4 + x^4*y^5*z^3 + x^5*y^3*z^4 + x^5*y^5*z^2 + x^6*y^2*z^4 + x^6*y^4*z^2

theorem root_row_14_0 : cartierP (component_14_1) (component_14_2) (component_14_3) = row_14_0 := by
  simp [cartierP,component_14_1,component_14_2,component_14_3,row_14_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_14_0 : symbolP (CharTwoFormal.source32 (3,1,0)) = row_14_0^2 := by
  rw [source_cartier_14,symbolP_cartierInput,root_row_14_0]

def row_14_1 : Poly := x*y^3*z^8 + x*y^5*z^6 + x*y^6*z^5 + x*y^8*z^3 + x^2*y^2*z^8 + x^2*y^3*z^7 + x^2*y^4*z^6 + x^2*y^5*z^5 + x^2*y^6*z^4 + x^2*y^8*z^2 + x^3*y^2*z^7 + x^3*y^4*z^5 + x^5*y^2*z^5 + x^5*y^4*z^3 + x^6*y^2*z^4 + x^6*y^4*z^2

theorem root_row_14_1 : cartierQ (component_14_1) (component_14_2) (component_14_3) = row_14_1 := by
  simp [cartierQ,component_14_1,component_14_2,component_14_3,row_14_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_14_1 : symbolQ (CharTwoFormal.source32 (3,1,0)) = row_14_1^2 := by
  rw [source_cartier_14,symbolQ_cartierInput,root_row_14_1]

def component_15_0 : Poly := x^2*y^3*z + x^3*y*z^2 + x^4*y^2*z
def component_15_1 : Poly := x*z^3 + x^2*y*z^2 + x^4*z^2
def component_15_2 : Poly := x^4*y*z
def component_15_3 : Poly := y*z^2

theorem source_cartier_15 : CharTwoFormal.source32 (3,1,1) = cartierInput (component_15_0) (component_15_1) (component_15_2) (component_15_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_15_0,component_15_1,component_15_2,component_15_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_15_0 : Poly := x*y^3*z^11 + x*y^7*z^7 + x^2*y^2*z^11 + x^2*y^3*z^10 + x^2*y^5*z^8 + x^2*y^7*z^6 + x^2*y^9*z^4 + x^2*y^10*z^3 + x^3*y^2*z^10 + x^3*y^3*z^9 + x^3*y^9*z^3 + x^3*y^10*z^2 + x^4*y^2*z^9 + x^4*y^4*z^7 + x^4*y^6*z^5 + x^4*y^8*z^3 + x^5*y^2*z^8 + x^5*y^4*z^6 + x^5*y^5*z^5 + x^5*y^6*z^4 + x^5*y^7*z^3 + x^5*y^8*z^2 + x^6*y^5*z^4 + x^6*y^7*z^2 + x^8*y^3*z^4 + x^8*y^5*z^2

theorem root_row_15_0 : cartierP (component_15_1) (component_15_2) (component_15_3) = row_15_0 := by
  simp [cartierP,component_15_1,component_15_2,component_15_3,row_15_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_15_0 : symbolP (CharTwoFormal.source32 (3,1,1)) = row_15_0^2 := by
  rw [source_cartier_15,symbolP_cartierInput,root_row_15_0]

def row_15_1 : Poly := x^2*y^3*z^10 + x^2*y^4*z^9 + x^2*y^9*z^4 + x^2*y^10*z^3 + x^3*y^2*z^10 + x^3*y^3*z^9 + x^3*y^9*z^3 + x^3*y^10*z^2 + x^4*y^3*z^8 + x^4*y^5*z^6 + x^4*y^6*z^5 + x^4*y^8*z^3 + x^5*y^2*z^8 + x^5*y^3*z^7 + x^5*y^4*z^6 + x^5*y^5*z^5 + x^5*y^6*z^4 + x^5*y^8*z^2 + x^6*y^2*z^7 + x^6*y^4*z^5 + x^8*y^2*z^5 + x^8*y^4*z^3

theorem root_row_15_1 : cartierQ (component_15_1) (component_15_2) (component_15_3) = row_15_1 := by
  simp [cartierQ,component_15_1,component_15_2,component_15_3,row_15_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_15_1 : symbolQ (CharTwoFormal.source32 (3,1,1)) = row_15_1^2 := by
  rw [source_cartier_15,symbolQ_cartierInput,root_row_15_1]

def component_16_0 : Poly := z^2
def component_16_1 : Poly := x^2*z
def component_16_2 : Poly := x*z
def component_16_3 : Poly := z

theorem source_cartier_16 : CharTwoFormal.source32 (4,0,0) = cartierInput (component_16_0) (component_16_1) (component_16_2) (component_16_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_16_0,component_16_1,component_16_2,component_16_3]
  ring_nf

def row_16_0 : Poly := x*y^2*z^7 + x*y^3*z^6 + x*y^4*z^5 + x*y^5*z^4 + x^2*y*z^7 + x^2*y^2*z^6 + x^2*y^4*z^4 + x^2*y^5*z^3 + x^4*y*z^5 + x^4*y^3*z^3

theorem root_row_16_0 : cartierP (component_16_1) (component_16_2) (component_16_3) = row_16_0 := by
  simp [cartierP,component_16_1,component_16_2,component_16_3,row_16_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_16_0 : symbolP (CharTwoFormal.source32 (4,0,0)) = row_16_0^2 := by
  rw [source_cartier_16,symbolP_cartierInput,root_row_16_0]

def row_16_1 : Poly := x*y^4*z^5 + x*y^5*z^4 + x*y^6*z^3 + x*y^7*z^2 + x^2*y^3*z^5 + x^2*y^4*z^4 + x^2*y^6*z^2 + x^2*y^7*z + x^4*y^3*z^3 + x^4*y^5*z

theorem root_row_16_1 : cartierQ (component_16_1) (component_16_2) (component_16_3) = row_16_1 := by
  simp [cartierQ,component_16_1,component_16_2,component_16_3,row_16_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_16_1 : symbolQ (CharTwoFormal.source32 (4,0,0)) = row_16_1^2 := by
  rw [source_cartier_16,symbolQ_cartierInput,root_row_16_1]

def component_17_0 : Poly := z^3 + x^3*z^2
def component_17_1 : Poly := x^2*z^2 + x^3*y*z
def component_17_2 : Poly := 0
def component_17_3 : Poly := x*y*z + x^3*z

theorem source_cartier_17 : CharTwoFormal.source32 (4,0,1) = cartierInput (component_17_0) (component_17_1) (component_17_2) (component_17_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_17_0,component_17_1,component_17_2,component_17_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_17_0 : Poly := x*y^4*z^8 + x*y^8*z^4 + x^2*y^2*z^9 + x^2*y^4*z^7 + x^2*y^5*z^6 + x^2*y^7*z^4 + x^3*y*z^9 + x^3*y^6*z^4 + x^3*y^7*z^3 + x^3*y^8*z^2 + x^4*y*z^8 + x^4*y^5*z^4 + x^5*y*z^7 + x^5*y^3*z^5 + x^5*y^4*z^4 + x^5*y^6*z^2 + x^6*y*z^6 + x^6*y^2*z^5 + x^6*y^3*z^4 + x^6*y^4*z^3

theorem root_row_17_0 : cartierP (component_17_1) (component_17_2) (component_17_3) = row_17_0 := by
  simp [cartierP,component_17_1,component_17_2,component_17_3,row_17_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_17_0 : symbolP (CharTwoFormal.source32 (4,0,1)) = row_17_0^2 := by
  rw [source_cartier_17,symbolP_cartierInput,root_row_17_0]

def row_17_1 : Poly := x*y^3*z^9 + x*y^7*z^5 + x^2*y^2*z^9 + x^2*y^3*z^8 + x^2*y^8*z^3 + x^2*y^9*z^2 + x^3*y^2*z^8 + x^3*y^3*z^7 + x^3*y^4*z^6 + x^3*y^9*z + x^4*y^2*z^7 + x^4*y^4*z^5 + x^4*y^6*z^3 + x^4*y^8*z + x^5*y^2*z^6 + x^5*y^4*z^4 + x^5*y^5*z^3 + x^5*y^7*z + x^6*y^3*z^4 + x^6*y^4*z^3 + x^6*y^5*z^2 + x^6*y^6*z

theorem root_row_17_1 : cartierQ (component_17_1) (component_17_2) (component_17_3) = row_17_1 := by
  simp [cartierQ,component_17_1,component_17_2,component_17_3,row_17_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_17_1 : symbolQ (CharTwoFormal.source32 (4,0,1)) = row_17_1^2 := by
  rw [source_cartier_17,symbolQ_cartierInput,root_row_17_1]

def component_18_0 : Poly := y*z^2
def component_18_1 : Poly := x*z^2 + x^2*y*z + x^4*z
def component_18_2 : Poly := z^2 + x*y*z + x^3*z
def component_18_3 : Poly := y*z

theorem source_cartier_18 : CharTwoFormal.source32 (4,1,0) = cartierInput (component_18_0) (component_18_1) (component_18_2) (component_18_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_18_0,component_18_1,component_18_2,component_18_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_18_0 : Poly := x*y^2*z^9 + x*y^4*z^7 + x*y^5*z^6 + x*y^7*z^4 + x^2*y*z^9 + x^2*y^2*z^8 + x^2*y^6*z^4 + x^2*y^7*z^3 + x^3*y*z^8 + x^3*y^2*z^7 + x^3*y^3*z^6 + x^3*y^4*z^5 + x^4*y^2*z^6 + x^4*y^3*z^5 + x^4*y^5*z^3 + x^4*y^6*z^2 + x^5*y*z^6 + x^5*y^2*z^5 + x^5*y^3*z^4 + x^5*y^4*z^3 + x^6*y*z^5 + x^6*y^2*z^4 + x^6*y^3*z^3 + x^6*y^4*z^2

theorem root_row_18_0 : cartierP (component_18_1) (component_18_2) (component_18_3) = row_18_0 := by
  simp [cartierP,component_18_1,component_18_2,component_18_3,row_18_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_18_0 : symbolP (CharTwoFormal.source32 (4,1,0)) = row_18_0^2 := by
  rw [source_cartier_18,symbolP_cartierInput,root_row_18_0]

def row_18_1 : Poly := x*y^3*z^8 + x*y^6*z^5 + x*y^8*z^3 + x*y^9*z^2 + x^2*y^2*z^8 + x^2*y^6*z^4 + x^2*y^7*z^3 + x^2*y^9*z + x^3*y^5*z^4 + x^3*y^6*z^3 + x^3*y^7*z^2 + x^3*y^8*z + x^4*y^3*z^5 + x^4*y^5*z^3 + x^5*y^3*z^4 + x^5*y^4*z^3 + x^5*y^5*z^2 + x^5*y^6*z + x^6*y^2*z^4 + x^6*y^3*z^3 + x^6*y^4*z^2 + x^6*y^5*z

theorem root_row_18_1 : cartierQ (component_18_1) (component_18_2) (component_18_3) = row_18_1 := by
  simp [cartierQ,component_18_1,component_18_2,component_18_3,row_18_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_18_1 : symbolQ (CharTwoFormal.source32 (4,1,0)) = row_18_1^2 := by
  rw [source_cartier_18,symbolQ_cartierInput,root_row_18_1]

def component_19_0 : Poly := y*z^3 + x^2*z^3 + x^3*y*z^2 + x^5*z^2
def component_19_1 : Poly := x^3*y^2*z + x^5*y*z
def component_19_2 : Poly := z^3 + x^3*z^2
def component_19_3 : Poly := x*y^2*z + x^2*z^2 + x^3*y*z + x^5*z

theorem source_cartier_19 : CharTwoFormal.source32 (4,1,1) = cartierInput (component_19_0) (component_19_1) (component_19_2) (component_19_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_19_0,component_19_1,component_19_2,component_19_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_19_0 : Poly := x*y^4*z^10 + x*y^5*z^9 + x*y^6*z^8 + x*y^8*z^6 + x*y^9*z^5 + x*y^10*z^4 + x^2*y^2*z^11 + x^2*y^3*z^10 + x^2*y^5*z^8 + x^2*y^8*z^5 + x^3*y*z^11 + x^3*y^3*z^9 + x^3*y^8*z^4 + x^3*y^10*z^2 + x^4*y^2*z^9 + x^4*y^3*z^8 + x^4*y^4*z^7 + x^4*y^5*z^6 + x^4*y^7*z^4 + x^4*y^9*z^2 + x^5*y*z^9 + x^5*y^6*z^4 + x^5*y^7*z^3 + x^5*y^8*z^2 + x^6*y*z^8 + x^6*y^2*z^7 + x^6*y^3*z^6 + x^6*y^4*z^5 + x^8*y*z^6 + x^8*y^2*z^5 + x^8*y^4*z^3 + x^8*y^5*z^2

theorem root_row_19_0 : cartierP (component_19_1) (component_19_2) (component_19_3) = row_19_0 := by
  simp [cartierP,component_19_1,component_19_2,component_19_3,row_19_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_19_0 : symbolP (CharTwoFormal.source32 (4,1,1)) = row_19_0^2 := by
  rw [source_cartier_19,symbolP_cartierInput,root_row_19_0]

def row_19_1 : Poly := x*y^3*z^11 + x*y^5*z^9 + x*y^6*z^8 + x*y^7*z^7 + x*y^9*z^5 + x*y^10*z^4 + x^2*y^2*z^11 + x^2*y^3*z^10 + x^2*y^4*z^9 + x^2*y^5*z^8 + x^2*y^6*z^7 + x^2*y^7*z^6 + x^2*y^10*z^3 + x^2*y^11*z^2 + x^3*y^2*z^10 + x^3*y^4*z^8 + x^3*y^9*z^3 + x^3*y^11*z + x^4*y^4*z^7 + x^4*y^7*z^4 + x^4*y^8*z^3 + x^4*y^9*z^2 + x^5*y^2*z^8 + x^5*y^3*z^7 + x^5*y^4*z^6 + x^5*y^9*z + x^6*y^5*z^4 + x^6*y^6*z^3 + x^6*y^7*z^2 + x^6*y^8*z + x^8*y^2*z^5 + x^8*y^3*z^4 + x^8*y^5*z^2 + x^8*y^6*z

theorem root_row_19_1 : cartierQ (component_19_1) (component_19_2) (component_19_3) = row_19_1 := by
  simp [cartierQ,component_19_1,component_19_2,component_19_3,row_19_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_19_1 : symbolQ (CharTwoFormal.source32 (4,1,1)) = row_19_1^2 := by
  rw [source_cartier_19,symbolQ_cartierInput,root_row_19_1]

def component_20_0 : Poly := x^2*y*z
def component_20_1 : Poly := x^3*z
def component_20_2 : Poly := x^2*z
def component_20_3 : Poly := x*z

theorem source_cartier_20 : CharTwoFormal.source32 (5,0,0) = cartierInput (component_20_0) (component_20_1) (component_20_2) (component_20_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_20_0,component_20_1,component_20_2,component_20_3]
  ring_nf

def row_20_0 : Poly := x*y^2*z^8 + x*y^6*z^4 + x^2*y*z^8 + x^2*y^3*z^6 + x^2*y^4*z^5 + x^2*y^6*z^3 + x^4*y*z^6 + x^4*y^2*z^5 + x^4*y^3*z^4 + x^4*y^4*z^3

theorem root_row_20_0 : cartierP (component_20_1) (component_20_2) (component_20_3) = row_20_0 := by
  simp [cartierP,component_20_1,component_20_2,component_20_3,row_20_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_20_0 : symbolP (CharTwoFormal.source32 (5,0,0)) = row_20_0^2 := by
  rw [source_cartier_20,symbolP_cartierInput,root_row_20_0]

def row_20_1 : Poly := x*y^4*z^6 + x*y^8*z^2 + x^2*y^3*z^6 + x^2*y^5*z^4 + x^2*y^6*z^3 + x^2*y^8*z + x^4*y^3*z^4 + x^4*y^4*z^3 + x^4*y^5*z^2 + x^4*y^6*z

theorem root_row_20_1 : cartierQ (component_20_1) (component_20_2) (component_20_3) = row_20_1 := by
  simp [cartierQ,component_20_1,component_20_2,component_20_3,row_20_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_20_1 : symbolQ (CharTwoFormal.source32 (5,0,0)) = row_20_1^2 := by
  rw [source_cartier_20,symbolQ_cartierInput,root_row_20_1]

def component_21_0 : Poly := x^3*y^2*z + x^4*z^2
def component_21_1 : Poly := x^3*z^2 + x^4*y*z
def component_21_2 : Poly := x^2*z^2 + x^3*y*z
def component_21_3 : Poly := x*z^2 + x^4*z

theorem source_cartier_21 : CharTwoFormal.source32 (5,0,1) = cartierInput (component_21_0) (component_21_1) (component_21_2) (component_21_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_21_0,component_21_1,component_21_2,component_21_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_21_0 : Poly := x*y^3*z^10 + x*y^4*z^9 + x*y^7*z^6 + x*y^8*z^5 + x^3*y*z^10 + x^3*y^3*z^8 + x^3*y^4*z^7 + x^3*y^6*z^5 + x^4*y*z^9 + x^4*y^6*z^4 + x^4*y^7*z^3 + x^4*y^8*z^2 + x^5*y*z^8 + x^5*y^3*z^6 + x^5*y^4*z^5 + x^5*y^6*z^3 + x^6*y*z^7 + x^6*y^3*z^5 + x^6*y^4*z^4 + x^6*y^6*z^2

theorem root_row_21_0 : cartierP (component_21_1) (component_21_2) (component_21_3) = row_21_0 := by
  simp [cartierP,component_21_1,component_21_2,component_21_3,row_21_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_21_0 : symbolP (CharTwoFormal.source32 (5,0,1)) = row_21_0^2 := by
  rw [source_cartier_21,symbolP_cartierInput,root_row_21_0]

def row_21_1 : Poly := x*y^3*z^10 + x*y^5*z^8 + x*y^7*z^6 + x*y^9*z^4 + x^2*y^2*z^10 + x^2*y^4*z^8 + x^2*y^8*z^4 + x^2*y^10*z^2 + x^3*y^5*z^6 + x^3*y^7*z^4 + x^3*y^8*z^3 + x^3*y^10*z + x^4*y^6*z^4 + x^4*y^7*z^3 + x^4*y^8*z^2 + x^4*y^9*z + x^5*y^3*z^6 + x^5*y^5*z^4 + x^5*y^6*z^3 + x^5*y^8*z + x^6*y^2*z^6 + x^6*y^4*z^4 + x^6*y^5*z^3 + x^6*y^7*z

theorem root_row_21_1 : cartierQ (component_21_1) (component_21_2) (component_21_3) = row_21_1 := by
  simp [cartierQ,component_21_1,component_21_2,component_21_3,row_21_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_21_1 : symbolQ (CharTwoFormal.source32 (5,0,1)) = row_21_1^2 := by
  rw [source_cartier_21,symbolQ_cartierInput,root_row_21_1]

def component_22_0 : Poly := x^2*y^2*z + x^3*z^2 + x^4*y*z
def component_22_1 : Poly := x^2*z^2 + x^3*y*z + x^5*z
def component_22_2 : Poly := x^4*z
def component_22_3 : Poly := x*y*z

theorem source_cartier_22 : CharTwoFormal.source32 (5,1,0) = cartierInput (component_22_0) (component_22_1) (component_22_2) (component_22_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_22_0,component_22_1,component_22_2,component_22_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_22_0 : Poly := x*y^2*z^10 + x*y^6*z^6 + x^2*y*z^10 + x^2*y^2*z^9 + x^2*y^7*z^4 + x^2*y^8*z^3 + x^3*y*z^9 + x^3*y^6*z^4 + x^3*y^7*z^3 + x^3*y^8*z^2 + x^4*y^2*z^7 + x^4*y^6*z^3 + x^5*y*z^7 + x^5*y^3*z^5 + x^5*y^4*z^4 + x^5*y^6*z^2 + x^6*y*z^6 + x^6*y^2*z^5 + x^6*y^3*z^4 + x^6*y^4*z^3

theorem root_row_22_0 : cartierP (component_22_1) (component_22_2) (component_22_3) = row_22_0 := by
  simp [cartierP,component_22_1,component_22_2,component_22_3,row_22_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_22_0 : symbolP (CharTwoFormal.source32 (5,1,0)) = row_22_0^2 := by
  rw [source_cartier_22,symbolP_cartierInput,root_row_22_0]

def row_22_1 : Poly := x*y^3*z^9 + x*y^4*z^8 + x*y^6*z^6 + x*y^7*z^5 + x*y^8*z^4 + x*y^10*z^2 + x^2*y^2*z^9 + x^2*y^6*z^5 + x^2*y^7*z^4 + x^2*y^8*z^3 + x^2*y^9*z^2 + x^2*y^10*z + x^3*y^2*z^8 + x^3*y^3*z^7 + x^3*y^4*z^6 + x^3*y^9*z + x^4*y^2*z^7 + x^4*y^3*z^6 + x^4*y^6*z^3 + x^4*y^7*z^2 + x^5*y^2*z^6 + x^5*y^4*z^4 + x^5*y^5*z^3 + x^5*y^7*z + x^6*y^3*z^4 + x^6*y^4*z^3 + x^6*y^5*z^2 + x^6*y^6*z

theorem root_row_22_1 : cartierQ (component_22_1) (component_22_2) (component_22_3) = row_22_1 := by
  simp [cartierQ,component_22_1,component_22_2,component_22_3,row_22_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_22_1 : symbolQ (CharTwoFormal.source32 (5,1,0)) = row_22_1^2 := by
  rw [source_cartier_22,symbolQ_cartierInput,root_row_22_1]

def component_23_0 : Poly := x^3*z^3 + x^3*y^3*z + x^5*y^2*z + x^6*z^2
def component_23_1 : Poly := x^2*z^3 + x^3*y*z^2 + x^4*y^2*z + x^6*y*z
def component_23_2 : Poly := x^2*y*z^2 + x^5*y*z
def component_23_3 : Poly := x*y*z^2 + x^6*z

theorem source_cartier_23 : CharTwoFormal.source32 (5,1,1) = cartierInput (component_23_0) (component_23_1) (component_23_2) (component_23_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_23_0,component_23_1,component_23_2,component_23_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_23_0 : Poly := x*y^3*z^12 + x*y^4*z^11 + x*y^7*z^8 + x*y^8*z^7 + x^2*y^3*z^11 + x^2*y^6*z^8 + x^2*y^7*z^7 + x^2*y^10*z^4 + x^3*y*z^12 + x^3*y^3*z^10 + x^3*y^8*z^5 + x^3*y^10*z^3 + x^4*y^3*z^9 + x^4*y^4*z^8 + x^4*y^7*z^5 + x^4*y^8*z^4 + x^5*y*z^10 + x^5*y^3*z^8 + x^5*y^4*z^7 + x^5*y^6*z^5 + x^6*y*z^9 + x^6*y^6*z^4 + x^6*y^7*z^3 + x^6*y^8*z^2 + x^8*y*z^7 + x^8*y^3*z^5 + x^8*y^4*z^4 + x^8*y^6*z^2

theorem root_row_23_0 : cartierP (component_23_1) (component_23_2) (component_23_3) = row_23_0 := by
  simp [cartierP,component_23_1,component_23_2,component_23_3,row_23_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_23_0 : symbolP (CharTwoFormal.source32 (5,1,1)) = row_23_0^2 := by
  rw [source_cartier_23,symbolP_cartierInput,root_row_23_0]

def row_23_1 : Poly := x*y^3*z^12 + x*y^5*z^10 + x*y^7*z^8 + x*y^9*z^6 + x^2*y^2*z^12 + x^2*y^4*z^10 + x^2*y^5*z^9 + x^2*y^9*z^5 + x^2*y^10*z^4 + x^2*y^12*z^2 + x^3*y^3*z^10 + x^3*y^5*z^8 + x^3*y^10*z^3 + x^3*y^12*z + x^4*y^2*z^10 + x^4*y^3*z^9 + x^4*y^4*z^8 + x^4*y^5*z^7 + x^4*y^7*z^5 + x^4*y^8*z^4 + x^4*y^9*z^3 + x^4*y^10*z^2 + x^5*y^5*z^6 + x^5*y^7*z^4 + x^5*y^8*z^3 + x^5*y^10*z + x^6*y^2*z^8 + x^6*y^3*z^7 + x^6*y^4*z^6 + x^6*y^9*z + x^8*y^2*z^6 + x^8*y^4*z^4 + x^8*y^5*z^3 + x^8*y^7*z

theorem root_row_23_1 : cartierQ (component_23_1) (component_23_2) (component_23_3) = row_23_1 := by
  simp [cartierQ,component_23_1,component_23_2,component_23_3,row_23_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_23_1 : symbolQ (CharTwoFormal.source32 (5,1,1)) = row_23_1^2 := by
  rw [source_cartier_23,symbolQ_cartierInput,root_row_23_1]

def component_24_0 : Poly := 0
def component_24_1 : Poly := 0
def component_24_2 : Poly := z^2 + x*y*z
def component_24_3 : Poly := 0

theorem source_cartier_24 : CharTwoFormal.source32 (6,0,0) = cartierInput (component_24_0) (component_24_1) (component_24_2) (component_24_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_24_0,component_24_1,component_24_2,component_24_3]
  ring_nf

def row_24_0 : Poly := x*y^3*z^8 + x*y^7*z^4 + x^2*y^2*z^8 + x^2*y^6*z^4 + x^3*y^5*z^4 + x^3*y^7*z^2 + x^4*y^4*z^4 + x^4*y^6*z^2 + x^5*y^3*z^4 + x^5*y^5*z^2 + x^6*y^2*z^4 + x^6*y^4*z^2

theorem root_row_24_0 : cartierP (component_24_1) (component_24_2) (component_24_3) = row_24_0 := by
  simp [cartierP,component_24_1,component_24_2,component_24_3,row_24_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_24_0 : symbolP (CharTwoFormal.source32 (6,0,0)) = row_24_0^2 := by
  rw [source_cartier_24,symbolP_cartierInput,root_row_24_0]

def row_24_1 : Poly := x^2*y^3*z^7 + x^2*y^4*z^6 + x^2*y^5*z^5 + x^2*y^6*z^4 + x^3*y^2*z^7 + x^3*y^4*z^5 + x^4*y^2*z^6 + x^4*y^3*z^5 + x^4*y^5*z^3 + x^4*y^6*z^2 + x^5*y^2*z^5 + x^5*y^4*z^3 + x^6*y^2*z^4 + x^6*y^4*z^2

theorem root_row_24_1 : cartierQ (component_24_1) (component_24_2) (component_24_3) = row_24_1 := by
  simp [cartierQ,component_24_1,component_24_2,component_24_3,row_24_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_24_1 : symbolQ (CharTwoFormal.source32 (6,0,0)) = row_24_1^2 := by
  rw [source_cartier_24,symbolQ_cartierInput,root_row_24_1]

def component_25_0 : Poly := x^2*z^3 + x^3*y*z^2
def component_25_1 : Poly := x*z^3 + x^2*y*z^2
def component_25_2 : Poly := z^3 + x^2*y^2*z
def component_25_3 : Poly := 0

theorem source_cartier_25 : CharTwoFormal.source32 (6,0,1) = cartierInput (component_25_0) (component_25_1) (component_25_2) (component_25_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_25_0,component_25_1,component_25_2,component_25_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_25_0 : Poly := x*y^4*z^10 + x*y^5*z^9 + x*y^8*z^6 + x*y^9*z^5 + x^2*y^3*z^10 + x^2*y^4*z^9 + x^2*y^5*z^8 + x^2*y^7*z^6 + x^2*y^8*z^5 + x^2*y^9*z^4 + x^3*y^6*z^6 + x^3*y^7*z^5 + x^3*y^8*z^4 + x^3*y^9*z^3 + x^4*y^3*z^8 + x^4*y^5*z^6 + x^4*y^6*z^5 + x^4*y^7*z^4 + x^4*y^8*z^3 + x^4*y^9*z^2 + x^5*y^4*z^6 + x^5*y^5*z^5 + x^5*y^6*z^4 + x^5*y^7*z^3 + x^6*y^3*z^6 + x^6*y^4*z^5 + x^6*y^5*z^4 + x^6*y^6*z^3 + x^8*y^3*z^4 + x^8*y^5*z^2

theorem root_row_25_0 : cartierP (component_25_1) (component_25_2) (component_25_3) = row_25_0 := by
  simp [cartierP,component_25_1,component_25_2,component_25_3,row_25_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_25_0 : symbolP (CharTwoFormal.source32 (6,0,1)) = row_25_0^2 := by
  rw [source_cartier_25,symbolP_cartierInput,root_row_25_0]

def row_25_1 : Poly := x^3*y^3*z^9 + x^3*y^4*z^8 + x^3*y^5*z^7 + x^3*y^6*z^6 + x^4*y^2*z^9 + x^4*y^3*z^8 + x^4*y^5*z^6 + x^4*y^6*z^5 + x^5*y^3*z^7 + x^5*y^4*z^6 + x^5*y^5*z^5 + x^5*y^6*z^4 + x^6*y^3*z^6 + x^6*y^4*z^5 + x^6*y^5*z^4 + x^6*y^6*z^3 + x^8*y^2*z^5 + x^8*y^4*z^3

theorem root_row_25_1 : cartierQ (component_25_1) (component_25_2) (component_25_3) = row_25_1 := by
  simp [cartierQ,component_25_1,component_25_2,component_25_3,row_25_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_25_1 : symbolQ (CharTwoFormal.source32 (6,0,1)) = row_25_1^2 := by
  rw [source_cartier_25,symbolQ_cartierInput,root_row_25_1]

def component_26_0 : Poly := x*z^3 + x^2*y*z^2
def component_26_1 : Poly := 0
def component_26_2 : Poly := y*z^2 + x*y^2*z + x^2*z^2 + x^3*y*z
def component_26_3 : Poly := 0

theorem source_cartier_26 : CharTwoFormal.source32 (6,1,0) = cartierInput (component_26_0) (component_26_1) (component_26_2) (component_26_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_26_0,component_26_1,component_26_2,component_26_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_26_0 : Poly := x*y^3*z^10 + x*y^4*z^9 + x*y^5*z^8 + x*y^7*z^6 + x*y^8*z^5 + x*y^9*z^4 + x^2*y^2*z^10 + x^2*y^3*z^9 + x^2*y^6*z^6 + x^2*y^7*z^5 + x^3*y^5*z^6 + x^3*y^6*z^5 + x^3*y^8*z^3 + x^3*y^9*z^2 + x^4*y^2*z^8 + x^4*y^4*z^6 + x^4*y^5*z^5 + x^4*y^7*z^3 + x^5*y^3*z^6 + x^5*y^4*z^5 + x^5*y^6*z^3 + x^5*y^7*z^2 + x^6*y^2*z^6 + x^6*y^3*z^5 + x^6*y^5*z^3 + x^6*y^6*z^2 + x^8*y^2*z^4 + x^8*y^4*z^2

theorem root_row_26_0 : cartierP (component_26_1) (component_26_2) (component_26_3) = row_26_0 := by
  simp [cartierP,component_26_1,component_26_2,component_26_3,row_26_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_26_0 : symbolP (CharTwoFormal.source32 (6,1,0)) = row_26_0^2 := by
  rw [source_cartier_26,symbolP_cartierInput,root_row_26_0]

def row_26_1 : Poly := x^2*y^3*z^9 + x^2*y^4*z^8 + x^2*y^5*z^7 + x^2*y^6*z^6 + x^3*y^2*z^9 + x^3*y^3*z^8 + x^3*y^5*z^6 + x^3*y^6*z^5 + x^5*y^2*z^7 + x^5*y^3*z^6 + x^5*y^5*z^4 + x^5*y^6*z^3 + x^6*y^2*z^6 + x^6*y^3*z^5 + x^6*y^5*z^3 + x^6*y^6*z^2 + x^8*y^2*z^4 + x^8*y^4*z^2

theorem root_row_26_1 : cartierQ (component_26_1) (component_26_2) (component_26_3) = row_26_1 := by
  simp [cartierQ,component_26_1,component_26_2,component_26_3,row_26_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_26_1 : symbolQ (CharTwoFormal.source32 (6,1,0)) = row_26_1^2 := by
  rw [source_cartier_26,symbolQ_cartierInput,root_row_26_1]

def component_27_0 : Poly := x*z^4 + x^2*y*z^3 + x^4*z^3 + x^5*y*z^2
def component_27_1 : Poly := x*y*z^3 + x^2*y^2*z^2 + x^3*z^3 + x^4*y*z^2
def component_27_2 : Poly := y*z^3 + x^2*y^3*z + x^3*y*z^2 + x^4*y^2*z
def component_27_3 : Poly := x*z^3 + x^2*y*z^2

theorem source_cartier_27 : CharTwoFormal.source32 (6,1,1) = cartierInput (component_27_0) (component_27_1) (component_27_2) (component_27_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_27_0,component_27_1,component_27_2,component_27_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_27_0 : Poly := x*y^4*z^12 + x*y^7*z^9 + x*y^8*z^8 + x*y^11*z^5 + x^2*y^3*z^12 + x^2*y^4*z^11 + x^2*y^8*z^7 + x^2*y^11*z^4 + x^3*y^4*z^10 + x^3*y^5*z^9 + x^3*y^10*z^4 + x^3*y^11*z^3 + x^4*y^2*z^11 + x^4*y^4*z^9 + x^4*y^5*z^8 + x^4*y^7*z^6 + x^4*y^9*z^4 + x^4*y^11*z^2 + x^5*y^2*z^10 + x^5*y^3*z^9 + x^5*y^6*z^6 + x^5*y^7*z^5 + x^5*y^8*z^4 + x^5*y^10*z^2 + x^6*y^5*z^6 + x^6*y^6*z^5 + x^6*y^8*z^3 + x^6*y^9*z^2 + x^8*y^2*z^7 + x^8*y^5*z^4 + x^8*y^6*z^3 + x^8*y^7*z^2 + x^9*y^2*z^6 + x^9*y^3*z^5 + x^9*y^5*z^3 + x^9*y^6*z^2 + x^10*y^3*z^4 + x^10*y^5*z^2

theorem root_row_27_0 : cartierP (component_27_1) (component_27_2) (component_27_3) = row_27_0 := by
  simp [cartierP,component_27_1,component_27_2,component_27_3,row_27_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_27_0 : symbolP (CharTwoFormal.source32 (6,1,1)) = row_27_0^2 := by
  rw [source_cartier_27,symbolP_cartierInput,root_row_27_0]

def row_27_1 : Poly := x^3*y^3*z^11 + x^3*y^4*z^10 + x^3*y^9*z^5 + x^3*y^10*z^4 + x^4*y^2*z^11 + x^4*y^4*z^9 + x^5*y^2*z^10 + x^5*y^4*z^8 + x^5*y^5*z^7 + x^5*y^6*z^6 + x^5*y^9*z^3 + x^5*y^10*z^2 + x^6*y^2*z^9 + x^6*y^3*z^8 + x^6*y^5*z^6 + x^6*y^6*z^5 + x^8*y^2*z^7 + x^8*y^3*z^6 + x^8*y^5*z^4 + x^8*y^6*z^3 + x^9*y^2*z^6 + x^9*y^3*z^5 + x^9*y^5*z^3 + x^9*y^6*z^2 + x^10*y^2*z^5 + x^10*y^4*z^3

theorem root_row_27_1 : cartierQ (component_27_1) (component_27_2) (component_27_3) = row_27_1 := by
  simp [cartierQ,component_27_1,component_27_2,component_27_3,row_27_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_27_1 : symbolQ (CharTwoFormal.source32 (6,1,1)) = row_27_1^2 := by
  rw [source_cartier_27,symbolQ_cartierInput,root_row_27_1]

def component_28_0 : Poly := 0
def component_28_1 : Poly := 0
def component_28_2 : Poly := x*z^2 + x^2*y*z
def component_28_3 : Poly := z^2 + x*y*z

theorem source_cartier_28 : CharTwoFormal.source32 (7,0,0) = cartierInput (component_28_0) (component_28_1) (component_28_2) (component_28_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_28_0,component_28_1,component_28_2,component_28_3]
  ring_nf

def row_28_0 : Poly := x*y^3*z^9 + x*y^4*z^8 + x*y^7*z^5 + x*y^8*z^4 + x^2*y^2*z^9 + x^2*y^4*z^7 + x^2*y^5*z^6 + x^2*y^7*z^4 + x^3*y^2*z^8 + x^3*y^4*z^6 + x^3*y^5*z^5 + x^3*y^6*z^4 + x^3*y^7*z^3 + x^3*y^8*z^2 + x^4*y^2*z^7 + x^4*y^3*z^6 + x^4*y^4*z^5 + x^4*y^7*z^2 + x^5*y^2*z^6 + x^5*y^3*z^5 + x^5*y^5*z^3 + x^5*y^6*z^2 + x^6*y^3*z^4 + x^6*y^5*z^2

theorem root_row_28_0 : cartierP (component_28_1) (component_28_2) (component_28_3) = row_28_0 := by
  simp [cartierP,component_28_1,component_28_2,component_28_3,row_28_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_28_0 : symbolP (CharTwoFormal.source32 (7,0,0)) = row_28_0^2 := by
  rw [source_cartier_28,symbolP_cartierInput,root_row_28_0]

def row_28_1 : Poly := x*y^4*z^8 + x*y^8*z^4 + x^3*y^2*z^8 + x^3*y^3*z^7 + x^3*y^4*z^6 + x^3*y^5*z^5 + x^3*y^6*z^4 + x^3*y^8*z^2 + x^4*y^2*z^7 + x^4*y^4*z^5 + x^5*y^2*z^6 + x^5*y^3*z^5 + x^5*y^5*z^3 + x^5*y^6*z^2 + x^6*y^2*z^5 + x^6*y^4*z^3

theorem root_row_28_1 : cartierQ (component_28_1) (component_28_2) (component_28_3) = row_28_1 := by
  simp [cartierQ,component_28_1,component_28_2,component_28_3,row_28_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_28_1 : symbolQ (CharTwoFormal.source32 (7,0,0)) = row_28_1^2 := by
  rw [source_cartier_28,symbolQ_cartierInput,root_row_28_1]

def component_29_0 : Poly := x*y*z^3 + x^2*y^2*z^2 + x^3*z^3 + x^4*y*z^2
def component_29_1 : Poly := 0
def component_29_2 : Poly := x*z^3 + x^3*y^2*z
def component_29_3 : Poly := z^3 + x^2*y^2*z

theorem source_cartier_29 : CharTwoFormal.source32 (7,0,1) = cartierInput (component_29_0) (component_29_1) (component_29_2) (component_29_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_29_0,component_29_1,component_29_2,component_29_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_29_0 : Poly := x*y^4*z^11 + x*y^6*z^9 + x*y^8*z^7 + x*y^10*z^5 + x^2*y^3*z^11 + x^2*y^6*z^8 + x^2*y^7*z^7 + x^2*y^10*z^4 + x^3*y^3*z^10 + x^3*y^4*z^9 + x^3*y^5*z^8 + x^3*y^10*z^3 + x^4*y^2*z^10 + x^4*y^4*z^8 + x^4*y^6*z^6 + x^4*y^10*z^2 + x^5*y^3*z^8 + x^5*y^5*z^6 + x^5*y^6*z^5 + x^5*y^8*z^3 + x^6*y^4*z^6 + x^6*y^5*z^5 + x^6*y^6*z^4 + x^6*y^7*z^3 + x^8*y^2*z^6 + x^8*y^3*z^5 + x^8*y^5*z^3 + x^8*y^6*z^2

theorem root_row_29_0 : cartierP (component_29_1) (component_29_2) (component_29_3) = row_29_0 := by
  simp [cartierP,component_29_1,component_29_2,component_29_3,row_29_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_29_0 : symbolP (CharTwoFormal.source32 (7,0,1)) = row_29_0^2 := by
  rw [source_cartier_29,symbolP_cartierInput,root_row_29_0]

def row_29_1 : Poly := x*y^5*z^10 + x*y^6*z^9 + x*y^9*z^6 + x*y^10*z^5 + x^2*y^4*z^10 + x^2*y^5*z^9 + x^2*y^6*z^8 + x^2*y^8*z^6 + x^2*y^9*z^5 + x^2*y^10*z^4 + x^3*y^3*z^10 + x^3*y^8*z^5 + x^3*y^9*z^4 + x^3*y^10*z^3 + x^4*y^2*z^10 + x^4*y^5*z^7 + x^4*y^6*z^6 + x^4*y^8*z^4 + x^4*y^9*z^3 + x^4*y^10*z^2 + x^5*y^3*z^8 + x^5*y^5*z^6 + x^5*y^6*z^5 + x^5*y^8*z^3 + x^6*y^3*z^7 + x^6*y^4*z^6 + x^6*y^5*z^5 + x^6*y^6*z^4 + x^8*y^2*z^6 + x^8*y^3*z^5 + x^8*y^5*z^3 + x^8*y^6*z^2

theorem root_row_29_1 : cartierQ (component_29_1) (component_29_2) (component_29_3) = row_29_1 := by
  simp [cartierQ,component_29_1,component_29_2,component_29_3,row_29_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_29_1 : symbolQ (CharTwoFormal.source32 (7,0,1)) = row_29_1^2 := by
  rw [source_cartier_29,symbolQ_cartierInput,root_row_29_1]

def component_30_0 : Poly := x^2*z^3 + x^3*y*z^2
def component_30_1 : Poly := x*z^3 + x^2*y*z^2
def component_30_2 : Poly := x*y*z^2 + x^2*y^2*z + x^3*z^2 + x^4*y*z
def component_30_3 : Poly := y*z^2 + x*y^2*z + x^2*z^2 + x^3*y*z

theorem source_cartier_30 : CharTwoFormal.source32 (7,1,0) = cartierInput (component_30_0) (component_30_1) (component_30_2) (component_30_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_30_0,component_30_1,component_30_2,component_30_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_30_0 : Poly := x*y^3*z^11 + x*y^6*z^8 + x*y^7*z^7 + x*y^10*z^4 + x^2*y^2*z^11 + x^2*y^3*z^10 + x^2*y^5*z^8 + x^2*y^8*z^5 + x^3*y^2*z^10 + x^3*y^3*z^9 + x^3*y^6*z^6 + x^3*y^7*z^5 + x^3*y^8*z^4 + x^3*y^10*z^2 + x^4*y^2*z^9 + x^4*y^3*z^8 + x^4*y^4*z^7 + x^4*y^6*z^5 + x^4*y^7*z^4 + x^4*y^8*z^3 + x^5*y^2*z^8 + x^5*y^8*z^2 + x^6*y^3*z^6 + x^6*y^4*z^5 + x^6*y^6*z^3 + x^6*y^7*z^2 + x^8*y^3*z^4 + x^8*y^5*z^2

theorem root_row_30_0 : cartierP (component_30_1) (component_30_2) (component_30_3) = row_30_0 := by
  simp [cartierP,component_30_1,component_30_2,component_30_3,row_30_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_30_0 : symbolP (CharTwoFormal.source32 (7,1,0)) = row_30_0^2 := by
  rw [source_cartier_30,symbolP_cartierInput,root_row_30_0]

def row_30_1 : Poly := x*y^4*z^10 + x*y^5*z^9 + x*y^6*z^8 + x*y^8*z^6 + x*y^9*z^5 + x*y^10*z^4 + x^2*y^4*z^9 + x^2*y^8*z^5 + x^3*y^2*z^10 + x^3*y^4*z^8 + x^3*y^5*z^7 + x^3*y^6*z^6 + x^3*y^9*z^3 + x^3*y^10*z^2 + x^4*y^3*z^8 + x^4*y^5*z^6 + x^4*y^6*z^5 + x^4*y^8*z^3 + x^5*y^2*z^8 + x^5*y^8*z^2 + x^6*y^2*z^7 + x^6*y^3*z^6 + x^6*y^5*z^4 + x^6*y^6*z^3 + x^8*y^2*z^5 + x^8*y^4*z^3

theorem root_row_30_1 : cartierQ (component_30_1) (component_30_2) (component_30_3) = row_30_1 := by
  simp [cartierQ,component_30_1,component_30_2,component_30_3,row_30_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_30_1 : symbolQ (CharTwoFormal.source32 (7,1,0)) = row_30_1^2 := by
  rw [source_cartier_30,symbolQ_cartierInput,root_row_30_1]

def component_31_0 : Poly := x*y^2*z^3 + x^2*z^4 + x^2*y^3*z^2 + x^4*y^2*z^2 + x^5*z^3 + x^6*y*z^2
def component_31_1 : Poly := x*z^4 + x^3*y^2*z^2
def component_31_2 : Poly := x^2*y^2*z^2 + x^3*y^3*z + x^4*y*z^2 + x^5*y^2*z
def component_31_3 : Poly := y*z^3 + x^2*z^3 + x^2*y^3*z + x^4*y^2*z

theorem source_cartier_31 : CharTwoFormal.source32 (7,1,1) = cartierInput (component_31_0) (component_31_1) (component_31_2) (component_31_3) := by
  simp [CharTwoFormal.source32,CharTwoFormal.compressedGenerator,
    CharTwoFormal.compressedBasis,CharTwoFormal.d4,CharTwoFormal.d6,
    CharTwoFormal.a,CharTwoFormal.b,CharTwoFormal.c,cartierInput,
    component_31_0,component_31_1,component_31_2,component_31_3]
  ring_nf
  simp only [ofNat_mod]
  norm_num

def row_31_0 : Poly := x*y^4*z^13 + x*y^5*z^12 + x*y^7*z^10 + x*y^9*z^8 + x*y^11*z^6 + x*y^12*z^5 + x^2*y^3*z^13 + x^2*y^5*z^11 + x^2*y^8*z^8 + x^2*y^9*z^7 + x^2*y^11*z^5 + x^2*y^12*z^4 + x^3*y^3*z^12 + x^3*y^6*z^9 + x^3*y^9*z^6 + x^3*y^12*z^3 + x^4*y^3*z^11 + x^4*y^6*z^8 + x^4*y^7*z^7 + x^4*y^8*z^6 + x^4*y^9*z^5 + x^4*y^10*z^4 + x^4*y^11*z^3 + x^4*y^12*z^2 + x^5*y^5*z^8 + x^5*y^11*z^2 + x^6*y^2*z^10 + x^6*y^3*z^9 + x^6*y^6*z^6 + x^6*y^7*z^5 + x^6*y^8*z^4 + x^6*y^10*z^2 + x^8*y^6*z^4 + x^8*y^8*z^2 + x^9*y^3*z^6 + x^9*y^4*z^5 + x^9*y^6*z^3 + x^9*y^7*z^2 + x^10*y^2*z^6 + x^10*y^3*z^5 + x^10*y^5*z^3 + x^10*y^6*z^2

theorem root_row_31_0 : cartierP (component_31_1) (component_31_2) (component_31_3) = row_31_0 := by
  simp [cartierP,component_31_1,component_31_2,component_31_3,row_31_0,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_31_0 : symbolP (CharTwoFormal.source32 (7,1,1)) = row_31_0^2 := by
  rw [source_cartier_31,symbolP_cartierInput,root_row_31_0]

def row_31_1 : Poly := x*y^5*z^12 + x*y^8*z^9 + x*y^9*z^8 + x*y^12*z^5 + x^2*y^4*z^12 + x^2*y^5*z^11 + x^2*y^9*z^7 + x^2*y^12*z^4 + x^3*y^3*z^12 + x^3*y^6*z^9 + x^3*y^9*z^6 + x^3*y^12*z^3 + x^4*y^2*z^12 + x^4*y^4*z^10 + x^4*y^6*z^8 + x^4*y^8*z^6 + x^4*y^10*z^4 + x^4*y^12*z^2 + x^5*y^2*z^11 + x^5*y^8*z^5 + x^6*y^2*z^10 + x^6*y^4*z^8 + x^6*y^5*z^7 + x^6*y^6*z^6 + x^6*y^9*z^3 + x^6*y^10*z^2 + x^8*y^2*z^8 + x^8*y^3*z^7 + x^8*y^4*z^6 + x^8*y^5*z^5 + x^8*y^6*z^4 + x^8*y^8*z^2 + x^9*y^2*z^7 + x^9*y^3*z^6 + x^9*y^5*z^4 + x^9*y^6*z^3 + x^10*y^2*z^6 + x^10*y^3*z^5 + x^10*y^5*z^3 + x^10*y^6*z^2

theorem root_row_31_1 : cartierQ (component_31_1) (component_31_2) (component_31_3) = row_31_1 := by
  simp [cartierQ,component_31_1,component_31_2,component_31_3,row_31_1,
    evalU,evalV,evalW,U,V,W,alpha,x,y,z]
  ring_nf
  simp only [ofNat_mod]
  norm_num

theorem symbol_row_31_1 : symbolQ (CharTwoFormal.source32 (7,1,1)) = row_31_1^2 := by
  rw [source_cartier_31,symbolQ_cartierInput,root_row_31_1]

def sourceIndex (i : Fin 32) : Fin 8 × Fin 2 × Fin 2 :=
  (⟨i.val / 4, by omega⟩, ⟨i.val / 2 % 2, by omega⟩, ⟨i.val % 2, by omega⟩)

def rootP : Fin 32 → Poly := ![row_0_0, row_1_0, row_2_0, row_3_0, row_4_0, row_5_0, row_6_0, row_7_0, row_8_0, row_9_0, row_10_0, row_11_0, row_12_0, row_13_0, row_14_0, row_15_0, row_16_0, row_17_0, row_18_0, row_19_0, row_20_0, row_21_0, row_22_0, row_23_0, row_24_0, row_25_0, row_26_0, row_27_0, row_28_0, row_29_0, row_30_0, row_31_0]

theorem symbolP_source (i : Fin 32) : symbolP (CharTwoFormal.source32 (sourceIndex i)) = (rootP i)^2 := by
  fin_cases i
  · exact symbol_row_0_0
  · exact symbol_row_1_0
  · exact symbol_row_2_0
  · exact symbol_row_3_0
  · exact symbol_row_4_0
  · exact symbol_row_5_0
  · exact symbol_row_6_0
  · exact symbol_row_7_0
  · exact symbol_row_8_0
  · exact symbol_row_9_0
  · exact symbol_row_10_0
  · exact symbol_row_11_0
  · exact symbol_row_12_0
  · exact symbol_row_13_0
  · exact symbol_row_14_0
  · exact symbol_row_15_0
  · exact symbol_row_16_0
  · exact symbol_row_17_0
  · exact symbol_row_18_0
  · exact symbol_row_19_0
  · exact symbol_row_20_0
  · exact symbol_row_21_0
  · exact symbol_row_22_0
  · exact symbol_row_23_0
  · exact symbol_row_24_0
  · exact symbol_row_25_0
  · exact symbol_row_26_0
  · exact symbol_row_27_0
  · exact symbol_row_28_0
  · exact symbol_row_29_0
  · exact symbol_row_30_0
  · exact symbol_row_31_0

def rootQ : Fin 32 → Poly := ![row_0_1, row_1_1, row_2_1, row_3_1, row_4_1, row_5_1, row_6_1, row_7_1, row_8_1, row_9_1, row_10_1, row_11_1, row_12_1, row_13_1, row_14_1, row_15_1, row_16_1, row_17_1, row_18_1, row_19_1, row_20_1, row_21_1, row_22_1, row_23_1, row_24_1, row_25_1, row_26_1, row_27_1, row_28_1, row_29_1, row_30_1, row_31_1]

theorem symbolQ_source (i : Fin 32) : symbolQ (CharTwoFormal.source32 (sourceIndex i)) = (rootQ i)^2 := by
  fin_cases i
  · exact symbol_row_0_1
  · exact symbol_row_1_1
  · exact symbol_row_2_1
  · exact symbol_row_3_1
  · exact symbol_row_4_1
  · exact symbol_row_5_1
  · exact symbol_row_6_1
  · exact symbol_row_7_1
  · exact symbol_row_8_1
  · exact symbol_row_9_1
  · exact symbol_row_10_1
  · exact symbol_row_11_1
  · exact symbol_row_12_1
  · exact symbol_row_13_1
  · exact symbol_row_14_1
  · exact symbol_row_15_1
  · exact symbol_row_16_1
  · exact symbol_row_17_1
  · exact symbol_row_18_1
  · exact symbol_row_19_1
  · exact symbol_row_20_1
  · exact symbol_row_21_1
  · exact symbol_row_22_1
  · exact symbol_row_23_1
  · exact symbol_row_24_1
  · exact symbol_row_25_1
  · exact symbol_row_26_1
  · exact symbol_row_27_1
  · exact symbol_row_28_1
  · exact symbol_row_29_1
  · exact symbol_row_30_1
  · exact symbol_row_31_1

end TernaryPoly.CharTwoSymbolRows
