module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Tree.Data
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Psi
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Edge
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Farey

@[expose] public section


/-!
# Lemma B.1, tree maps: the linear maps on the permutation modules of the Farey tree

Formalized by Claude Sonnet 5.5.

The classes `F2 t ∈ Φ(RG₂)` of the Farey triangles and `F3 e ∈ Φ(RG₃)` of the oriented edges (`CellFarey`, `CellEdge`) are extended
linearly to the permutation modules `P0 = ℚ[Tri]` and `PE = ℚ[OTE]` (`F2lin`, `F3lin`).  They satisfy the determinant-twisted
equivariance `F(π(q) c) = det(π(q)) · q F(c)` (`F2lin_equiv`, `F3lin_equiv`) and the boundary relations
`Φ(d₃) F3lin = F2lin dTilde` (`dPhi_F3lin`).
-/

open CategoryTheory MonoidalCategory Representation Limits
open scoped TensorProduct

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.HochschildSerre
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames

/-- The determinant of the block of `q ∈ P_H/U`, as a rational number. -/
def detQ (q : PH ⧸ U) : ℚ := (((pibar q).val.det : ℤ) : ℚ)

theorem detQ_mul_self (q : PH ⧸ U) : detQ q * detQ q = 1 := by
  unfold detQ
  rcases det_pm (pibar q) with h | h <;> simp [h]

theorem detQ_mul (q r : PH ⧸ U) : detQ (q * r) = detQ q * detQ r := by
  unfold detQ
  rw [map_mul, Units.val_mul, Matrix.det_mul]
  push_cast
  rfl

theorem detQ_one : detQ 1 = 1 := by
  unfold detQ
  rw [map_one]
  simp

/-- The determinant character of `P_H/U` (through `pibar`), as a representation on `ℚ`. -/
def detRep : Representation ℚ (PH ⧸ U) ℚ where
  toFun q := detQ q • LinearMap.id
  map_one' := by rw [detQ_one, one_smul]; rfl
  map_mul' q r := by
    rw [detQ_mul, Module.End.mul_eq_comp, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    rfl

/-- The one-dimensional representation `L` of `P_H/U` by the determinant of the block. -/
def Ldet : Rep.{0} ℚ (PH ⧸ U) := Rep.of detRep

theorem Ldet_ρ (q : PH ⧸ U) (a : Ldet.V) : Ldet.ρ q a = detQ q • a := rfl

/-! ### Linear extensions -/

/-- The linear extension of `t ↦ F2 t` to `P0 = ℚ[Tri]`. -/
def F2lin : P0.V →ₗ[ℚ] (PhiX 2).V :=
  (Finsupp.linearCombination ℚ F2) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

/-- The linear extension of `e ↦ F3 e` to `PE = ℚ[OTE]`. -/
def F3lin : PE.V →ₗ[ℚ] (PhiX 3).V :=
  (Finsupp.linearCombination ℚ F3) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem F2lin_single (t : Tri) (r : ℚ) : F2lin (MonoidAlgebra.single t r) = r • F2 t := by
  simp [F2lin]

theorem F3lin_single (e : OTE) (r : ℚ) : F3lin (MonoidAlgebra.single e r) = r • F3 e := by
  simp [F3lin]


theorem detQ_mk (g : PH) : detQ (QuotientGroup.mk g : PH ⧸ U) = (((pi g).val.det : ℤ) : ℚ) := rfl

theorem F2lin_equiv (q : PH ⧸ U) (c : P0.V) :
    F2lin (P0.ρ (pibar q) c) = detQ q • (PhiX 2).ρ q (F2lin c) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]
  | single t r =>
    have h1 : P0.ρ (pibar (QuotientGroup.mk g)) (MonoidAlgebra.single t r) =
        MonoidAlgebra.single (pi g • t) r := Representation.ofMulAction_single _ _ _
    rw [h1, F2lin_single, F2lin_single, F2_smul_eq g t, map_smul, detQ_mk]
    exact smul_comm _ _ _

theorem F3lin_equiv (q : PH ⧸ U) (c : PE.V) :
    F3lin (PE.ρ (pibar q) c) = detQ q • (PhiX 3).ρ q (F3lin c) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]
  | single p r =>
    have h1 : PE.ρ (pibar (QuotientGroup.mk g)) (MonoidAlgebra.single p r) =
        MonoidAlgebra.single (pi g • p) r := Representation.ofMulAction_single _ _ _
    rw [h1, F3lin_single, F3lin_single, F3_smul_eq g p, map_smul, detQ_mk]
    exact smul_comm _ _ _

theorem dPhi_F3lin (c : PE.V) : (dPhi 2).hom (F3lin c) = F2lin (dTilde.hom c) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  | single p r =>
    rw [F3lin_single, map_smul, F3_boundary, dTilde_single, map_sub, F2lin_single, F2lin_single, smul_sub]

theorem dPhi1_F2lin (c : P0.V) :
    ((TernaryPeriodPolynomials.Argument.HochschildSerre.Phi U).map
      ((Rep.resFunctor PH.subtype).map (dRG 1))).hom (F2lin c) = 0 := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | single t r => rw [F2lin_single, map_smul, F2_boundary, smul_zero]

theorem psi_F2lin (ψ : (PhiX 2).V →ₗ[ℚ] ℚ) (hψ : ∀ t, ψ (F2 t) = 1) (c : P0.V) :
    ψ (F2lin c) = epsMap.hom c := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | single t r => rw [F2lin_single, map_smul, hψ, epsMap_single, smul_eq_mul, mul_one]

end TernaryPeriodPolynomials.Argument.AppendixBResidue
