module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.CommonRootRadicals

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryParabolicGroups
open Matrix ModThreeGoodAction RelativeStabilizerCoordinates RelativeStabilizerMatrices
open RelativeStabilizerParameters RelativeStabilizerConsumer RadicalFirstCohomologyLattice

/-- The full integral plane parabolic; no residue or scalar-one condition is imposed. -/
def P : Subgroup IntegralGL := stabilizer P0
/-- The full integral line parabolic; its lower block is unrestricted GL₂(ℤ). -/
def Q : Subgroup IntegralGL := stabilizer L0
/-- The actual full upper triangular intersection. -/
def B : Subgroup IntegralGL := P ⊓ Q

@[simp] theorem mem_P (g : IntegralGL) : g ∈ P ↔ g.val 2 0 = 0 ∧ g.val 2 1 = 0 :=
  stabilizes_P0_iff g
@[simp] theorem mem_Q (g : IntegralGL) : g ∈ Q ↔ g.val 1 0 = 0 ∧ g.val 2 0 = 0 :=
  stabilizes_L0_iff g
@[simp] theorem mem_B (g : IntegralGL) :
    g ∈ B ↔ g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0 := by
  simp only [B,Subgroup.mem_inf,mem_P,mem_Q]
  tauto

/-- The literal full plane block matrix, retaining its independent last scalar. -/
def planeMatrix (A : Mat2) (u : Fin 2 → ℤ) (ε : ℤ) : Mat :=
  !![A 0 0,A 0 1,u 0;A 1 0,A 1 1,u 1;0,0,ε]

theorem det_planeMatrix (A : Mat2) (u : Fin 2 → ℤ) (ε : ℤ) :
    (planeMatrix A u ε).det = A.det * ε := by
  rw [Matrix.det_fin_three,Matrix.det_fin_two]
  simp [planeMatrix]
  ring

def planeElement (A : GL2) (u : Fin 2 → ℤ) (ε : ℤˣ) : IntegralGL :=
  GeneralLinearGroup.mk'' (planeMatrix A.val u ε.val) (by
    rw [det_planeMatrix]
    exact (GeneralLinearGroup.det A).isUnit.mul ε.isUnit)

@[simp] theorem planeElement_val (A : GL2) (u : Fin 2 → ℤ) (ε : ℤˣ) :
    (planeElement A u ε).val = planeMatrix A.val u ε.val := GeneralLinearGroup.val_mk'' _ _

theorem planeElement_mem (A : GL2) (u : Fin 2 → ℤ) (ε : ℤˣ) : planeElement A u ε ∈ P := by
  simp [planeMatrix]

theorem lineElement_mem (ε : ℤˣ) (u : Fin 2 → ℤ) (D : GL2) : lineElement ε u D ∈ Q := by
  simp [RelativeStabilizerMatrices.lineMatrix]

/-- Literal parametrization of the full plane parabolic, with all unit signs retained. -/
theorem mem_P_iff_parameter (g : IntegralGL) : g ∈ P ↔
    ∃ (A : GL2) (u : Fin 2 → ℤ) (ε : ℤˣ), g = planeElement A u ε := by
  constructor
  · intro hg
    obtain ⟨h20,h21⟩ := (mem_P g).mp hg
    have he : g.val = planeMatrix (topBlock g) ![g.val 0 2,g.val 1 2] (g.val 2 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [planeMatrix,topBlock,h20,h21]
    have hd := det_isUnit g
    rw [he,det_planeMatrix] at hd
    let A := GeneralLinearGroup.mk'' (topBlock g) (unit_of_mul_left hd)
    let ε := (unit_of_mul_right hd).unit
    refine ⟨A,![g.val 0 2,g.val 1 2],ε,?_⟩
    apply Units.ext
    rw [planeElement_val]
    change g.val = planeMatrix (GeneralLinearGroup.mk'' _ _).val _ (unit_of_mul_right hd).unit.val
    rw [GeneralLinearGroup.val_mk'',IsUnit.unit_spec]
    exact he
  · rintro ⟨A,u,ε,rfl⟩
    exact planeElement_mem A u ε

/-- Literal parametrization of the full line parabolic, without a congruence condition on GL₂. -/
theorem mem_Q_iff_parameter (g : IntegralGL) : g ∈ Q ↔
    ∃ (ε : ℤˣ) (u : Fin 2 → ℤ) (D : GL2), g = lineElement ε u D := by
  constructor
  · intro hg
    obtain ⟨h10,h20⟩ := (mem_Q g).mp hg
    have he : g.val = lineMatrix (g.val 0 0) ![g.val 0 1,g.val 0 2] (bottomBlock g) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lineMatrix,bottomBlock,h10,h20]
    have hd := det_isUnit g
    rw [he,det_lineMatrix] at hd
    let ε := (unit_of_mul_left hd).unit
    let D := GeneralLinearGroup.mk'' (bottomBlock g) (unit_of_mul_right hd)
    refine ⟨ε,![g.val 0 1,g.val 0 2],D,?_⟩
    apply Units.ext
    rw [lineElement_val]
    change g.val = lineMatrix (unit_of_mul_left hd).unit.val _ (GeneralLinearGroup.mk'' _ _).val
    rw [IsUnit.unit_spec,GeneralLinearGroup.val_mk'']
    exact he
  · rintro ⟨ε,u,D,rfl⟩
    exact lineElement_mem ε u D

theorem planeRadical_le_P : planeRadical ≤ P := by
  rintro g ⟨u,rfl⟩
  simp [planeHom,RelativeStabilizerMatrices.planeMatrix]

theorem lineRadical_le_Q : lineRadical ≤ Q := by
  rintro g ⟨u,rfl⟩
  exact lineElement_mem _ _ _

theorem commonRoot_le_B : OrdinaryBoundaryCommonRoot.commonRoot ≤ B := by
  rw [OrdinaryBoundaryCommonRoot.commonRoot_eq_intersection]
  exact inf_le_inf planeRadical_le_P lineRadical_le_Q

theorem commonRoot_le_planeRadical : OrdinaryBoundaryCommonRoot.commonRoot ≤ planeRadical := by
  rw [OrdinaryBoundaryCommonRoot.commonRoot_eq_intersection]
  exact inf_le_left

theorem commonRoot_le_lineRadical : OrdinaryBoundaryCommonRoot.commonRoot ≤ lineRadical := by
  rw [OrdinaryBoundaryCommonRoot.commonRoot_eq_intersection]
  exact inf_le_right

end TernaryPoly.OrdinaryParabolicGroups
