module

public import TernaryPeriodPolynomials.SymmetricSolution.Odd.TowerHomogeneous
public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Scaling

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricOddRationalTower
open SymmetricOddRationalSeed

variable {k : ℕ}

/-- The rational seed belongs to the actual degree-n single-pole module for every
nonzero linear denominator and arbitrary linear second and third coordinates. -/
theorem pValue_mem_singlePole {n : ℕ} (q : Fin k → BP)
    (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    (v : ModThreeGoodAction.Space) (hv : v≠0) (b c : TP)
    (hb : b.IsHomogeneous 1) (hc : c.IsHomogeneous 1) :
    pValue q (SinglePole.form v) b c ∈ SinglePole.singlePole n := by
  exact SinglePole.fraction_mem_singlePole n v hv
    ⟨numerator q (SinglePole.form v) b c,
      numerator_homogeneous q hq hd (SinglePole.form_homogeneous v) hb hc⟩

theorem form_coordinate (i : Fin 3) : SinglePole.form (Pi.single i 1)=X i := by
  fin_cases i <;> simp [SinglePole.form,Pi.single_apply]

/-- Every coordinate placement of P is an actual degree-n single-pole coefficient. -/
theorem pValue_coordinates_mem_singlePole {n : ℕ} (q : Fin k → BP)
    (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) (i j l : Fin 3) :
    pValue q (X i) (X j) (X l) ∈ SinglePole.singlePole n := by
  have hv : (Pi.single i 1 : ModThreeGoodAction.Space)≠0 := by
    intro h
    have hi := congrFun h i
    simp at hi
  simpa only [form_coordinate] using pValue_mem_singlePole q hq hd (Pi.single i 1) hv
    (X j) (X l) (isHomogeneous_X ℚ j) (isHomogeneous_X ℚ l)

/-- The polynomial Q seed is an actual homogeneous member of the same single-pole module. -/
theorem qPolynomial_mem_singlePole {n : ℕ} (q : Fin k → BP)
    (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) :
    embed (qPolynomial q hq) ∈ SinglePole.singlePole n := by
  simpa only [SinglePole.polynomialInclusion_val] using (SinglePole.polynomialInclusion n ⟨qPolynomial q hq,qPolynomial_homogeneous q hq hd⟩).property

/-- The exact regular correction is likewise a homogeneous polynomial coefficient. -/
theorem regular_mem_singlePole {n : ℕ} (q : Fin k → BP)
    (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ))) (i j l : Fin 3) :
    embed (regular q (X i) (X j) (X l)) ∈ SinglePole.singlePole n := by
  simpa only [SinglePole.polynomialInclusion_val] using (SinglePole.polynomialInclusion n
    ⟨regular q (X i) (X j) (X l),regular_homogeneous q hq hd
      (isHomogeneous_X ℚ i) (X_ne_zero i) (isHomogeneous_X ℚ j) (isHomogeneous_X ℚ l)⟩).property

end TernaryPoly.SymmetricOddRationalTower
