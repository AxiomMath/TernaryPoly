module

public import TernaryPeriodPolynomials.SymmetricSolution.LineCohomology.Twist

@[expose] public section

open CategoryTheory MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.SymmetricLineCohomology
open RadicalCoinvariantAlgebra RadicalFirstCohomologyLattice LatticeTopCohomology
open RelativeStabilizerParameters RelativeStabilizerMatrices groupCohomology

/-- Inverse conjugation by diag(t,L) on the integral row lattice. -/
def leviLatticeChange (t : ℤˣ) (L : GL2) : Lattice →* Lattice where
  toFun g := Multiplicative.ofAdd
    ((t⁻¹).val * (g.toAdd.1 * L.val 0 0 + g.toAdd.2 * L.val 1 0),
     (t⁻¹).val * (g.toAdd.1 * L.val 0 1 + g.toAdd.2 * L.val 1 1))
  map_one' := by simp
  map_mul' g h := by
    change (_,_) = (_,_)
    congr 1 <;> dsimp <;> ring

/-- The displayed row operation is literal conjugation of actual integral matrices. -/
theorem leviLatticeChange_commute (t : ℤˣ) (L : GL2) (g : Lattice) :
    lineElement t 0 L * lineHom (leviLatticeChange t L g) =
      lineHom g * lineElement t 0 L := by
  rcases Int.units_eq_one_or t with rfl | rfl <;>
    apply Units.ext <;> simp only [Units.val_mul,lineElement_val] <;>
    ext i j <;> rw [Matrix.mul_apply,Matrix.mul_apply] <;>
    fin_cases i <;> fin_cases j <;>
    simp [lineHom,lineElement_val,lineMatrix,leviLatticeChange,Fin.sum_univ_three]

theorem leviLatticeChange_conjugation (t : ℤˣ) (L : GL2) (g : Lattice) :
    lineHom (leviLatticeChange t L g) =
      (lineElement t 0 L)⁻¹ * lineHom g * lineElement t 0 L := by
  have h := congrArg (fun z => (lineElement t 0 L)⁻¹ * z)
    (leviLatticeChange_commute t L g)
  simpa [mul_assoc] using h

/-- Genuine twisted normalizer action on the lattice coefficient representation. -/
def leviCoefficientHom (n : ℕ) (t : ℤˣ) (L : GL2) :
    Rep.res (leviLatticeChange t L) (lineRep n) ⟶ lineRep n :=
  Rep.ofHom ⟨PolynomialGLAction.integralAction n (-1) (lineElement t 0 L), by
    intro g
    change PolynomialGLAction.integralAction n (-1) (lineElement t 0 L) *
      (lineRep n).ρ (leviLatticeChange t L g) =
      (lineRep n).ρ g * PolynomialGLAction.integralAction n (-1) (lineElement t 0 L)
    rw [← lineHom_action_twist n (-1),← lineHom_action_twist n (-1),
      ← map_mul,← map_mul,leviLatticeChange_commute]⟩

def latticeH1LeviAction (n : ℕ) (t : ℤˣ) (L : GL2) :
    groupCohomology (lineRep n) 1 ⟶ groupCohomology (lineRep n) 1 :=
  groupCohomology.map (leviLatticeChange t L) (leviCoefficientHom n t L) 1

/-- The corresponding genuine subgroup homomorphism is inverse ambient conjugation. -/
def leviSubgroupChange (t : ℤˣ) (L : GL2) : lineRadical →* lineRadical :=
  lineParamEquiv.toMonoidHom.comp ((leviLatticeChange t L).comp lineParamEquiv.symm.toMonoidHom)

@[simp] theorem leviSubgroupChange_parameter (t : ℤˣ) (L : GL2) (g : Lattice) :
    leviSubgroupChange t L (lineParamEquiv g) = lineParamEquiv (leviLatticeChange t L g) := by
  simp [leviSubgroupChange]

theorem leviSubgroupChange_conjugation (t : ℤˣ) (L : GL2) (g : lineRadical) :
    (leviSubgroupChange t L g).val = (lineElement t 0 L)⁻¹ * g.val * lineElement t 0 L := by
  obtain ⟨g,rfl⟩ := lineParamEquiv.surjective g
  rw [leviSubgroupChange_parameter]
  exact leviLatticeChange_conjugation t L g

/-- The determinant exponent is minus one also on the normalizer coefficient map. -/
def leviSubgroupCoefficientHom (n : ℕ) (t : ℤˣ) (L : GL2) :
    Rep.res (leviSubgroupChange t L) (twistedSubgroupRep n) ⟶ twistedSubgroupRep n :=
  Rep.ofHom ⟨PolynomialGLAction.integralAction n (-1) (lineElement t 0 L), by
    intro g
    change PolynomialGLAction.integralAction n (-1) (lineElement t 0 L) *
      PolynomialGLAction.integralAction n (-1) (leviSubgroupChange t L g).val =
      PolynomialGLAction.integralAction n (-1) g.val *
        PolynomialGLAction.integralAction n (-1) (lineElement t 0 L)
    rw [← map_mul,← map_mul,leviSubgroupChange_conjugation]
    simp only [← mul_assoc,mul_inv_cancel,one_mul]⟩

def subgroupH1LeviAction (n : ℕ) (t : ℤˣ) (L : GL2) :
    groupCohomology (twistedSubgroupRep n) 1 ⟶ groupCohomology (twistedSubgroupRep n) 1 :=
  groupCohomology.map (leviSubgroupChange t L) (leviSubgroupCoefficientHom n t L) 1

/-- Parameterization commutes with the actual inverse-conjugation cocycle maps. -/
theorem levi_cocycles_parameter (n : ℕ) (t : ℤˣ) (L : GL2)
    (c : cocycles₁ (twistedSubgroupRep n)) :
    mapCocycles₁ (leviLatticeChange t L) (leviCoefficientHom n t L)
      (mapCocycles₁ lineParamEquiv.toMonoidHom (twistedParameterCoefficient n) c) =
    mapCocycles₁ lineParamEquiv.toMonoidHom (twistedParameterCoefficient n)
      (mapCocycles₁ (leviSubgroupChange t L) (leviSubgroupCoefficientHom n t L) c) := by
  apply cocycles₁_ext
  intro g
  change PolynomialGLAction.integralAction n (-1) (lineElement t 0 L)
      (c (lineParamEquiv (leviLatticeChange t L g))) =
    PolynomialGLAction.integralAction n (-1) (lineElement t 0 L)
      (c (leviSubgroupChange t L (lineParamEquiv g)))
  rw [leviSubgroupChange_parameter]

end TernaryPoly.SymmetricLineCohomology
