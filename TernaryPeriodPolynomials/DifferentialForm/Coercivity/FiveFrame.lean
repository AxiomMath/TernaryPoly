module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.BaseContraction
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SixVanishing

@[expose] public section



/-! Combinatorial frame machinery for the degree-5 (k=4) basepoint contraction bound: an explicit
"move index `i0` to the front" permutation table on `Fin 5`, and the two facts it is used for
(a repeated-argument vanishing fact, and a sign-squared pairing identity).
-/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering
open TernaryPoly.SL3PolynomialCoercivity

/-- Row `i0` lists `i0` followed by `Fin 5 \ {i0}` in increasing order. -/
def moveFrontTable : Fin 5 → Fin 5 → Fin 5 :=
  ![![0,1,2,3,4], ![1,0,2,3,4], ![2,0,1,3,4], ![3,0,1,2,4], ![4,0,1,2,3]]

theorem moveFrontTable_zero (i0 : Fin 5) : moveFrontTable i0 0 = i0 := by
  fin_cases i0 <;> rfl

theorem moveFrontTable_bijective (i0 : Fin 5) : Function.Bijective (moveFrontTable i0) := by
  fin_cases i0 <;> decide

/-- The permutation of `Fin 5` given by row `i0` of `moveFrontTable`. -/
def moveFrontEquiv (i0 : Fin 5) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (moveFrontTable i0) (moveFrontTable_bijective i0)

theorem moveFrontEquiv_apply (i0 r : Fin 5) : moveFrontEquiv i0 r = moveFrontTable i0 r := rfl

/-- The 4-tuple of basis vectors omitting index `i0`, in the table's order. -/
def sectorFrame (i0 : Fin 5) : Fin 4 → Coordinates := fun r => baseFrame (moveFrontTable i0 r.succ)

theorem vecCons_sectorFrame (i0 : Fin 5) :
    Matrix.vecCons (baseFrame i0) (sectorFrame i0) = fun r => baseFrame (moveFrontEquiv i0 r) := by
  funext r
  refine Fin.cases ?_ ?_ r
  · simp [moveFrontEquiv_apply, moveFrontTable_zero]
  · intro r'
    simp [sectorFrame, moveFrontEquiv_apply]

/-- For `i ≠ i0`, `baseFrame i` already occurs in the sector tuple, so prepending it repeats an
argument and the alternating value is zero. -/
theorem formValue_five_vecCons_sectorFrame_eq_zero (n : ℕ) (a : FormValue n 5)
    (i0 i : Fin 5) (hi : i ≠ i0) :
    a (Matrix.vecCons (baseFrame i) (sectorFrame i0)) = 0 := by
  set r : Fin 5 := (moveFrontEquiv i0).symm i with hr
  have hrr : moveFrontEquiv i0 r = i := (moveFrontEquiv i0).apply_symm_apply i
  have hr0 : r ≠ 0 := by
    intro h
    exact hi (by rw [← hrr, h, moveFrontEquiv_apply, moveFrontTable_zero])
  obtain ⟨r', hr'⟩ := Fin.eq_succ_of_ne_zero hr0
  have hval : Matrix.vecCons (baseFrame i) (sectorFrame i0) r = baseFrame i := by
    rw [hr']
    show sectorFrame i0 r' = baseFrame i
    rw [sectorFrame, ← moveFrontEquiv_apply, ← hr', hrr]
  have h0 : Matrix.vecCons (baseFrame i) (sectorFrame i0) 0 = baseFrame i := by
    simp
  exact AlternatingMap.map_eq_zero_of_eq a.toAlternatingMap _ (h0.trans hval.symm) (Ne.symm hr0)

/-- `Equiv.Perm.sign` applied to any real-vector-space-valued alternating map value squares away
under a (bi-)linear self-pairing: `factorialPairing` of a `sign • x` with itself equals that of
`x` with itself. -/
theorem factorialPairing_sign_smul_self (σ : Equiv.Perm (Fin 5)) (x : Poly) :
    factorialPairing (Equiv.Perm.sign σ • x) (Equiv.Perm.sign σ • x) = factorialPairing x x := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

end TernaryPeriodPolynomials.Argument.Coercivity
