module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.ToddSymbol

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoToddSymbol

/-- A supplied four-component expression; no decomposition theorem is assumed here. -/
def cartierInput (A B C E : Poly) : Poly :=
  A^2 + X 1*B^2 + X 0*X 2*C^2 + X 0*X 1*X 2*E^2

def cartierP (B C E : Poly) : Poly :=
  U*evalU B + z*U*evalU C + y*z*U*evalU E + z*V*evalV B +
    y*z*alpha*V*evalV E + W*evalW B + alpha*z*W*evalW E

def cartierQ (B C E : Poly) : Poly :=
  y*U*evalU C + y*z*U*evalU E + y*V*evalV B + y*alpha*V*evalV C +
    W*evalW B + alpha*W*evalW C

private theorem ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly) = ((n % 2 : ℕ) : Poly) := CharP.cast_eq_mod Poly 2 n

theorem cartierInput_pderiv_one (A B C E : Poly) :
    pderiv 1 (cartierInput A B C E) = B^2+X 0*X 2*E^2 := by
  simp [cartierInput,CharTwo.two_eq_zero]
  ring

theorem cartierInput_pderiv_two (A B C E : Poly) :
    pderiv 2 (cartierInput A B C E) = X 0*C^2+X 0*X 1*E^2 := by
  simp [cartierInput,CharTwo.two_eq_zero]
  ring

theorem reducedSymbol_cartierInput (A B C E : Poly) :
    reducedSymbol (cartierInput A B C E) = y*(cartierP B C E)^2+z*(cartierQ B C E)^2 := by
  simp only [reducedSymbol,cartierInput_pderiv_one,cartierInput_pderiv_two,
    map_add,map_mul,map_pow]
  have hu0 : evalU (X 0) = alpha := by simp [evalU]
  have hu1 : evalU (X 1) = x^2+x*y+y*z := by simp [evalU]
  have hu2 : evalU (X 2) = z*x*(x+y) := by simp [evalU]
  have hv0 : evalV (X 0) = alpha := by simp [evalV]
  have hv1 : evalV (X 1) = x^2+x*z+y*z := by simp [evalV]
  have hv2 : evalV (X 2) = x*y*(x+z) := by simp [evalV]
  have hw0 : evalW (X 0) = alpha := by simp [evalW]
  have hw1 : evalW (X 1) = x^2+x*y+z^2 := by simp [evalW]
  have hw2 : evalW (X 2) = z*(x+z)*(x+y+z) := by simp [evalW]
  rw [hu0,hu1,hu2,hv0,hv1,hv2,hw0,hw1,hw2]
  simp only [cartierP,cartierQ,alpha]
  ring_nf
  simp only [ofNat_mod]
  norm_num

/-- The differential rows are squares when the source is given in four components. -/
theorem symbolP_cartierInput (A B C E : Poly) :
    symbolP (cartierInput A B C E) = (cartierP B C E)^2 := by
  rw [symbolP,reducedSymbol_cartierInput]
  simp [CharTwo.two_eq_zero,y,z]

theorem symbolQ_cartierInput (A B C E : Poly) :
    symbolQ (cartierInput A B C E) = (cartierQ B C E)^2 := by
  rw [symbolQ,reducedSymbol_cartierInput]
  simp [CharTwo.two_eq_zero,y,z]

end TernaryPoly.CharTwoToddSymbol
