module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.FacePairingBase
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.LineFaces
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneCusps
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.GammaNCoordinate

@[expose] public section


/-!
# The Levi acts on the radical lattice of every face with determinant one

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

For the line group `Γ(N) ∩ Q(ℤ)` the Levi element `A ∈ Γ₂(N)` acts on the radical lattice by the row vector action
`(a, b) ↦ (a, b) A` (`lineRadicalInput_toAdd`), for the plane group by `r ↦ A⁻¹ r`; both have determinant one
(`lineRadicalInput_det`, `planeRadicalInput_det`), and so do the conjugate faces `h⁻¹ Q h`, `h⁻¹ P h`
(`lineFaceRadicalInput_det`, `planeFaceRadicalInput_det`).  This is the hypothesis of `radPairingOf_levi`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces
open scoped MatrixGroups

section Line

variable (N : ℕ) [NeZero N]

theorem lineRadicalInput_toAdd (A : ↥(CongruenceSubgroup.Gamma N)) (r : RadicalLattice) :
    (splitRadicalInput (lineSplitting N) A r).toAdd.1 =
        r.toAdd.1 * (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + r.toAdd.2 * (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
      (splitRadicalInput (lineSplitting N) A r).toAdd.2 =
        r.toAdd.1 * (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + r.toAdd.2 * (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
  have h := splitRadicalInput_commute (lineSplitting N) A r
  generalize splitRadicalInput (lineSplitting N) A r = q at h ⊢
  have h' : (radEltQ N r * blockDiagQ A.1 : SL(3, ℤ)) = blockDiagQ A.1 * radEltQ N q :=
    congrArg (fun g : ↥(gammaNQ N) => (g : SL(3, ℤ))) h
  have h'' := congrArg (fun g : SL(3, ℤ) => (g : Matrix (Fin 3) (Fin 3) ℤ)) h'
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h''
  have e01 := congrFun (congrFun h'' 0) 1
  have e02 := congrFun (congrFun h'' 0) 2
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp [radEltQ, blockDiagQ, Matrix.mul_apply, Fin.sum_univ_three] at e01 e02
  constructor
  · apply mul_left_cancel₀ hN
    linear_combination -e01
  · apply mul_left_cancel₀ hN
    linear_combination -e02

/-- **The Levi `Γ₂(N)` acts on the radical lattice of the line group with determinant one.** -/
theorem lineRadicalInput_det (A : ↥(CongruenceSubgroup.Gamma N)) :
    radDet (splitRadicalInput (lineSplitting N) A) = 1 := by
  obtain ⟨a1, a2⟩ := lineRadicalInput_toAdd N A rl1
  obtain ⟨b1, b2⟩ := lineRadicalInput_toAdd N A rl2
  have hdet : (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := A.1.det_coe
    rwa [Matrix.det_fin_two] at this
  have r1 : rl1.toAdd = (1, 0) := rfl
  have r2 : rl2.toAdd = (0, 1) := rfl
  simp only [radDet, a1, a2, b1, b2, r1, r2]
  linear_combination hdet

end Line

section Conj

open TernaryPeriodPolynomials.Argument.SeedC3S4c

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ))

theorem lineFaceRadicalInput_det (A : ↥(CongruenceSubgroup.Gamma N)) :
    radDet (splitRadicalInput (lineFaceSplitting N h) A) = 1 := by
  have : splitRadicalInput (lineFaceSplitting N h) A = splitRadicalInput (lineSplitting N) A :=
    MonoidHom.ext fun r => FaceTransport.radicalInput_eq (lineFaceEquiv N h) (lineSplitting N) A r
  rw [this]
  exact lineRadicalInput_det N A

theorem planeRadicalInput_det (A : ↥(CongruenceSubgroup.Gamma N)) :
    radDet (splitRadicalInput (gammaNSplitting N) A) = 1 := by
  have hdet : (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (A.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := A.1.det_coe
    rwa [Matrix.det_fin_two] at this
  have hinv : ∀ i j, ((Matrix.SpecialLinearGroup.toGL A.1)⁻¹ : GL (Fin 2) ℤ).val i j =
      (A.1 : Matrix (Fin 2) (Fin 2) ℤ).adjugate i j := fun i j => rfl
  have : splitRadicalInput (gammaNSplitting N) A = upperLeviLatticeInput (Matrix.SpecialLinearGroup.toGL A.1) :=
    MonoidHom.ext fun r => gammaN_radicalInput N A r
  rw [this]
  simp only [radDet, upperLeviLatticeInput, MonoidHom.coe_mk, OneHom.coe_mk, rl1, rl2, radicalLatticeFirst,
    radicalLatticeSecond, hinv, Matrix.adjugate_fin_two, toAdd_ofAdd]
  simp
  linear_combination hdet

theorem planeFaceRadicalInput_det (A : ↥(CongruenceSubgroup.Gamma N)) :
    radDet (splitRadicalInput (faceSplitting N h) A) = 1 := by
  have : splitRadicalInput (faceSplitting N h) A = splitRadicalInput (gammaNSplitting N) A :=
    MonoidHom.ext fun r => FaceTransport.radicalInput_eq (faceEquiv N h) (gammaNSplitting N) A r
  rw [this]
  exact planeRadicalInput_det N A

end Conj

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
