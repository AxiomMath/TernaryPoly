module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Parabolic.GroupsBasic
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.CohomologySemidirect

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryParabolicGroups
open Matrix ModThreeGoodAction RelativeStabilizerParameters RelativeStabilizerMatrices
open RadicalFirstCohomologyLattice

abbrev PlaneLevi := GL2 × ℤˣ
abbrev LineLevi := ℤˣ × GL2

/-- The full plane Levi embedding, including the independent last scalar. -/
def planeLevi : PlaneLevi →* IntegralGL where
  toFun q := planeElement q.1 0 q.2
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [planeElement_val,planeMatrix]
  map_mul' q r := by
    apply Units.ext
    simp only [Units.val_mul,planeElement_val]
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      simp [planeMatrix,Matrix.mul_apply,Fin.sum_univ_three,Fin.sum_univ_two]

/-- The full line Levi embedding; the lower GL₂ block is unrestricted. -/
def lineLevi : LineLevi →* IntegralGL where
  toFun q := lineElement q.1 0 q.2
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lineElement_val,lineMatrix]
  map_mul' q r := by
    apply Units.ext
    simp only [Units.val_mul,lineElement_val]
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      simp [lineMatrix,Matrix.mul_apply,Fin.sum_univ_three,Fin.sum_univ_two]

theorem plane_radical_levi (M : GL2) (ε : ℤˣ) (u : Fin 2 → ℤ) :
    RelativeStabilizerParameters.planeElement 1 u * planeElement M 0 ε =
      planeElement M (ε.val • u) ε := by
  apply Units.ext
  simp only [Units.val_mul,planeElement_val,RelativeStabilizerParameters.planeElement_val]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [planeMatrix,RelativeStabilizerMatrices.planeMatrix,Fin.sum_univ_three,mul_comm]

theorem plane_levi_radical (M : GL2) (ε : ℤˣ) (u : Fin 2 → ℤ) :
    planeElement M 0 ε * RelativeStabilizerParameters.planeElement 1 u =
      planeElement M (M.val.mulVec u) ε := by
  apply Units.ext
  simp only [Units.val_mul,planeElement_val,RelativeStabilizerParameters.planeElement_val]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [planeMatrix,RelativeStabilizerMatrices.planeMatrix,Matrix.mulVec,dotProduct,
      Fin.sum_univ_three,Fin.sum_univ_two]

/-- Forward conjugation acts by `u ↦ ε⁻¹ M u` on the actual column radical. -/
theorem plane_levi_conjugate (M : GL2) (ε : ℤˣ) (u : Fin 2 → ℤ) :
    planeElement M 0 ε * RelativeStabilizerParameters.planeElement 1 u *
      (planeElement M 0 ε)⁻¹ =
      RelativeStabilizerParameters.planeElement 1 ((ε⁻¹).val • M.val.mulVec u) := by
  apply (mul_right_cancel_iff (a := planeElement M 0 ε)).mp
  rw [mul_assoc,inv_mul_cancel,mul_one,plane_levi_radical,plane_radical_levi]
  congr 1
  ext i
  simp [Pi.smul_apply,←mul_assoc,←Units.val_mul]

/-- Forward conjugation acts by `u ↦ ε u D⁻¹` on the actual row radical. -/
theorem line_levi_conjugate (ε : ℤˣ) (D : GL2) (u : Fin 2 → ℤ) :
    lineElement ε 0 D * lineElement 1 u 1 * (lineElement ε 0 D)⁻¹ =
      lineElement 1 (Matrix.vecMul (ε.val • u) (D⁻¹).val) 1 :=
  RelativeVertexCohomology.line_levi_conjugate ε D u

def planeNormalizer : PlaneLevi →* (Subgroup.normalizer (planeRadical : Set IntegralGL)) :=
  RelativeVertexCohomology.normalizerHom planeRadical planeLevi (by
    intro q n hn
    obtain ⟨u,rfl⟩ := hn
    change planeElement q.1 0 q.2 * RelativeStabilizerParameters.planeElement 1
      ![u.toAdd.1,u.toAdd.2] * (planeElement q.1 0 q.2)⁻¹ ∈ planeRadical
    rw [plane_levi_conjugate]
    let v := (q.2⁻¹).val • q.1.val.mulVec ![u.toAdd.1,u.toAdd.2]
    refine ⟨Multiplicative.ofAdd (v 0,v 1),?_⟩
    change RelativeStabilizerParameters.planeElement 1 ![v 0,v 1] =
      RelativeStabilizerParameters.planeElement 1 v
    congr 1
    funext i
    fin_cases i <;> rfl)

def lineNormalizer : LineLevi →* (Subgroup.normalizer (lineRadical : Set IntegralGL)) :=
  RelativeVertexCohomology.normalizerHom lineRadical lineLevi (by
    intro q n hn
    obtain ⟨u,rfl⟩ := hn
    change lineElement q.1 0 q.2 * lineElement 1 ![u.toAdd.1,u.toAdd.2] 1 *
      (lineElement q.1 0 q.2)⁻¹ ∈ lineRadical
    rw [line_levi_conjugate]
    let v := Matrix.vecMul (q.1.val • ![u.toAdd.1,u.toAdd.2]) (q.2⁻¹).val
    refine ⟨Multiplicative.ofAdd (v 0,v 1),?_⟩
    change lineElement 1 ![v 0,v 1] 1 = lineElement 1 v 1
    congr 1
    funext i
    fin_cases i <;> rfl)

/-- The full plane Levi acts by actual forward matrix conjugation. -/
def planeAction : PlaneLevi →* MulAut planeRadical :=
  planeRadical.normalizerMonoidHom.comp planeNormalizer
/-- The full line Levi acts by actual forward matrix conjugation. -/
def lineAction : LineLevi →* MulAut lineRadical :=
  lineRadical.normalizerMonoidHom.comp lineNormalizer

@[simp] theorem planeAction_val (q : PlaneLevi) (u : planeRadical) :
    (planeAction q u).val = planeLevi q * u.val * (planeLevi q)⁻¹ := rfl
@[simp] theorem lineAction_val (q : LineLevi) (u : lineRadical) :
    (lineAction q u).val = lineLevi q * u.val * (lineLevi q)⁻¹ := rfl

theorem planeLevi_mem (q : PlaneLevi) : planeLevi q ∈ P := planeElement_mem _ _ _
theorem lineLevi_mem (q : LineLevi) : lineLevi q ∈ Q := lineElement_mem _ _ _

end TernaryPoly.OrdinaryParabolicGroups
