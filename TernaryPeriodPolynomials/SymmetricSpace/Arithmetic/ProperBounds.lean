module

public import TernaryPeriodPolynomials.SymmetricSpace.Positive
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceArithmeticProper
open Matrix SymmetricSpacePositive
abbrev Vector := Fin 3 → ℝ

/-- The actual positive quadratic form, with the standard real star omitted by equality. -/
def quadratic (S : Mat) (x : Vector) : ℝ := x ⬝ᵥ (S*ᵥx)

@[simp] theorem quadratic_zero (S : Mat) : quadratic S 0 = 0 := by
  simp [quadratic]

theorem quadratic_pos (S : Mat) (hS : S.PosDef) (x : Vector) (hx : x ≠ 0) :
    0 < quadratic S x := by
  simpa only [quadratic,star_trivial] using hS.dotProduct_mulVec_pos hx

/-- Homogeneity is proved for the actual quadratic form, not imposed as a bound hypothesis. -/
theorem quadratic_smul (S : Mat) (r : ℝ) (x : Vector) :
    quadratic S (r • x) = r^2 * quadratic S x := by
  simp only [quadratic,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

/-- Joint continuity in the actual positive form and its vector. -/
theorem continuous_quadratic : Continuous (fun p : Space × Vector => quadratic p.1.val p.2) :=
  continuous_snd.dotProduct ((continuous_subtype_val.comp continuous_fst).matrix_mulVec continuous_snd)

/-- Every compact family of positive forms is uniformly coercive. No closedness away from
zero or properness of an arithmetic action is assumed: compactness of the unit sphere supplies it. -/
theorem compact_uniform_coercivity (C : Set Space) (hC : IsCompact C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ S ∈ C, ∀ x : Vector, ε*‖x‖^2 ≤ quadratic S.val x := by
  have hk := hC.prod (isCompact_sphere (0 : Vector) 1)
  obtain ⟨ε,hε,hbound⟩ := hk.exists_forall_le' continuous_quadratic.continuousOn (a := (0 : ℝ)) (by
    intro p hp
    apply quadratic_pos p.1.val p.1.property.1 p.2
    intro he
    have hh := hp.2
    simp [he] at hh)
  refine ⟨ε,hε,?_⟩
  intro S hS x
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let y : Vector := ‖x‖⁻¹ • x
  have hy : y ∈ Metric.sphere (0 : Vector) 1 := by
    simp only [Metric.mem_sphere,dist_zero_right]
    simp [y,norm_smul,norm_inv,hn]
  have hb := hbound (S,y) ⟨hS,hy⟩
  have hrec : ‖x‖ • y = x := by
    simp [y,smul_smul,hn]
  calc
    ε*‖x‖^2 ≤ quadratic S.val y*‖x‖^2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    _ = quadratic S.val x := by rw [mul_comm,←quadratic_smul,hrec]

/-- The determinant stays uniformly strictly positive on every compact family of positive forms. -/
theorem compact_det_lower (C : Set Space) (hC : IsCompact C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S ∈ C, δ ≤ S.val.det :=
  hC.exists_forall_le' continuous_subtype_val.matrix_det.continuousOn
    (fun S _ => S.property.1.det_pos)

/-- The determinant has a uniform upper bound on a compact family, including an empty family. -/
theorem compact_det_upper (C : Set Space) (hC : IsCompact C) :
    ∃ M : ℝ, ∀ S ∈ C, S.val.det ≤ M := by
  obtain ⟨M,hM⟩ := hC.bddAbove_image continuous_subtype_val.matrix_det.continuousOn
  exact ⟨M,fun S hS => hM ⟨S,hS,rfl⟩⟩

/-- A trace-one positive form has every diagonal entry bounded by one. -/
theorem diagonal_le_one (S : Space) (i : Fin 3) : S.val i i ≤ 1 := by
  have h : S.val i i ≤ ∑ j : Fin 3, S.val j j :=
    Finset.single_le_sum (fun j _ => le_of_lt (S.property.1.diag_pos (i := j))) (Finset.mem_univ i)
  change S.val i i ≤ S.val.trace at h
  rwa [S.property.2] at h

end TernaryPoly.SymmetricSpaceArithmeticProper
