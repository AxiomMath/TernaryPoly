module

public import Mathlib.GroupTheory.SemidirectProduct
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLattice
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantLevi

@[expose] public section


open CategoryTheory CategoryTheory.Limits Matrix
noncomputable section
namespace TernaryPoly.RelativeVertexCohomology
open ModThreeGoodAction RelativeStabilizerParameters RelativeStabilizerMatrices
open RelativeStabilizerConsumer RadicalFirstCohomologyLattice RadicalCoinvariantAlgebra
open LatticeTopCohomology

/-- Lift a genuine conjugating group into the actual subgroup normalizer. -/
def normalizerHom {H Q : Type} [Group H] [Group Q] (R : Subgroup H) (ι : Q →* H)
    (h : ∀ q n, n ∈ R → ι q * n * (ι q)⁻¹ ∈ R) : Q →* (Subgroup.normalizer (R : Set H)) where
  toFun q := ⟨ι q, by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨h q n, fun hn => ?_⟩
    have he := h q⁻¹ (ι q*n*(ι q)⁻¹) hn
    simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel,
      mul_one] using he⟩
  map_one' := Subtype.ext ι.map_one
  map_mul' q r := Subtype.ext (ι.map_mul q r)

/-- The exact plane Levi block embedding. -/
def planeLevi : GL2 →* IntegralGL where
  toFun M := planeElement M 0
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [planeElement_val,planeMatrix]
  map_mul' M D := by
    apply Units.ext
    simp only [Units.val_mul,planeElement_val]
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      simp [planeMatrix,Matrix.mul_apply,Fin.sum_univ_three,Fin.sum_univ_two]

/-- The exact line Levi block embedding, including its independent line sign. -/
def lineLevi : (ℤˣ × Gamma) →* IntegralGL where
  toFun q := lineElement q.1 0 q.2.val
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

theorem plane_radical_levi (M : GL2) (u : Fin 2 → ℤ) :
    planeElement 1 u * planeElement M 0 = planeElement M u := by
  apply Units.ext
  simp only [Units.val_mul,planeElement_val]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [planeMatrix,Fin.sum_univ_three]

theorem line_radical_levi (ε : ℤˣ) (D : GL2) (u : Fin 2 → ℤ) :
    lineElement 1 u 1 * lineElement ε 0 D = lineElement ε (Matrix.vecMul u D.val) D := by
  apply Units.ext
  simp only [Units.val_mul,lineElement_val]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [lineMatrix,Matrix.vecMul,dotProduct,Fin.sum_univ_three,Fin.sum_univ_two]

theorem line_levi_radical (ε : ℤˣ) (D : GL2) (u : Fin 2 → ℤ) :
    lineElement ε 0 D * lineElement 1 u 1 = lineElement ε (ε.val • u) D := by
  apply Units.ext
  simp only [Units.val_mul,lineElement_val]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [lineMatrix,Fin.sum_univ_three]

/-- Literal line-radical conjugation on its row parameters. -/
theorem line_levi_conjugate (ε : ℤˣ) (D : GL2) (u : Fin 2 → ℤ) :
    lineElement ε 0 D * lineElement 1 u 1 * (lineElement ε 0 D)⁻¹ =
      lineElement 1 (Matrix.vecMul (ε.val • u) (D⁻¹).val) 1 := by
  apply (mul_right_cancel_iff (a := lineElement ε 0 D)).mp
  rw [mul_assoc, inv_mul_cancel, mul_one, line_levi_radical, line_radical_levi,
    Matrix.vecMul_vecMul]
  have hD : (D⁻¹).val * D.val = 1 := by rw [← Units.val_mul,inv_mul_cancel,Units.val_one]
  rw [hD, Matrix.vecMul_one]

def planeNormalizer : GL2 →* (Subgroup.normalizer (planeRadical : Set IntegralGL)) :=
  normalizerHom planeRadical planeLevi (by
    intro M n hn
    obtain ⟨u,rfl⟩ := hn
    change planeElement M 0 * planeElement 1 ![u.toAdd.1,u.toAdd.2] *
      (planeElement M 0)⁻¹ ∈ planeRadical
    rw [planeLevi_radical_conjugate]
    let v := M.val.mulVec ![u.toAdd.1,u.toAdd.2]
    refine ⟨Multiplicative.ofAdd (v 0,v 1), ?_⟩
    change planeElement 1 ![v 0,v 1] = planeElement 1 v
    congr 1
    funext i
    fin_cases i <;> rfl)

def lineNormalizer : (ℤˣ × Gamma) →* (Subgroup.normalizer (lineRadical : Set IntegralGL)) :=
  normalizerHom lineRadical lineLevi (by
    intro q n hn
    obtain ⟨u,rfl⟩ := hn
    change lineElement q.1 0 q.2.val * lineElement 1 ![u.toAdd.1,u.toAdd.2] 1 *
      (lineElement q.1 0 q.2.val)⁻¹ ∈ lineRadical
    rw [line_levi_conjugate]
    let v := Matrix.vecMul (q.1.val • ![u.toAdd.1,u.toAdd.2]) (q.2.val⁻¹).val
    refine ⟨Multiplicative.ofAdd (v 0,v 1), ?_⟩
    change lineElement 1 ![v 0,v 1] 1 = lineElement 1 v 1
    congr 1
    funext i
    fin_cases i <;> rfl)

/-- Actual forward conjugation on the literal integral radical subgroups. -/
def planeAction : GL2 →* MulAut planeRadical :=
  planeRadical.normalizerMonoidHom.comp planeNormalizer

def lineAction : (ℤˣ × Gamma) →* MulAut lineRadical :=
  lineRadical.normalizerMonoidHom.comp lineNormalizer

@[simp] theorem planeAction_val (M : GL2) (u : planeRadical) :
    (planeAction M u).val = planeLevi M * u.val * (planeLevi M)⁻¹ := rfl

@[simp] theorem lineAction_val (q : ℤˣ × Gamma) (u : lineRadical) :
    (lineAction q u).val = lineLevi q * u.val * (lineLevi q)⁻¹ := rfl

end TernaryPoly.RelativeVertexCohomology
