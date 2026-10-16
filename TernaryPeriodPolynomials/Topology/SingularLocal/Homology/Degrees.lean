module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Free
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Data.Finsupp.ToDFinsupp

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalHomology
open scoped Classical
open CategoryTheory FreeActionLinearization CoveringSingularOrbits

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep ℚ G)

/-- The genuine geometric local-coefficient chain module: the dependent finite direct sum over
actual singular simplices downstairs of their actual first-vertex coefficient fibers. -/
abbrev VertexChain (n : ℕ) := Π₀ σ : SingularSimplex B n, FiberCoefficient p hp V (atVertex σ)

/-- A chosen genuine simplex lift, obtained from the proved orbit/simplex bijection. -/
def chosenLift (n : ℕ) (σ : SingularSimplex B n) : Lifts p σ := by
  let q := (orbitEquiv p hp n).symm σ
  refine ⟨q.out, ?_⟩
  change orbitEquiv p hp n (Quotient.mk _ q.out) = σ
  rw [Quotient.out_eq]
  exact (orbitEquiv p hp n).apply_symm_apply σ

/-- Evaluation in the actual coefficient fiber at the actual vertex of the chosen lift. -/
def chosenEvaluation (n : ℕ) (σ : SingularSimplex B n) :
    FiberCoefficient p hp V (atVertex σ) ≃ₗ[ℚ] V :=
  coefficientEvaluationLinearEquiv p hp (liftVertexEquiv p hp σ (chosenLift p hp n σ))

/-- Actual fiber evaluation identifies the dependent finite direct sum with finitely supported
vectors, without changing its indexing by literal base singular simplices. -/
def vertexCoefficientEquiv (n : ℕ) : VertexChain p hp V n ≃ₗ[ℚ] (SingularSimplex B n →₀ V) := by
  classical
  exact (DFinsupp.mapRange.linearEquiv (chosenEvaluation p hp V n)) ≪≫ₗ
    (finsuppLequivDFinsupp ℚ).symm

/-- A geometric elementary chain evaluates to the single vector at the same actual simplex. -/
theorem vertexCoefficientEquiv_single (n : ℕ) (σ : SingularSimplex B n)
    (c : FiberCoefficient p hp V (atVertex σ)) :
    vertexCoefficientEquiv p hp V n (DFinsupp.single σ c) =
      Finsupp.single σ (chosenEvaluation p hp V n σ c) := by
  classical
  simp [vertexCoefficientEquiv]

variable [IsCancelSMul G E]

/-- The actual degreewise isomorphism from coinvariant singular chains to genuine geometric
finite sums of actual vertex-fiber coefficients. -/
def degreeEquiv (n : ℕ) : (coinvariantChains G E V).X n ≃ₗ[ℚ] VertexChain p hp V n :=
  orbitCoefficientEquiv G E V n ≪≫ₗ Finsupp.domLCongr (R := ℚ) (orbitEquiv p hp n) ≪≫ₗ
    (vertexCoefficientEquiv p hp V n).symm

/-- The inverse identification sends a geometric elementary chain to its actual chosen-lift tensor. -/
theorem degreeEquiv_symm_single (n : ℕ) (σ : SingularSimplex B n)
    (c : FiberCoefficient p hp V (atVertex σ)) :
    (degreeEquiv p hp V n).symm (DFinsupp.single σ c) =
      generator G E V n (chosenLift p hp n σ).val (chosenEvaluation p hp V n σ c) := by
  classical
  change (orbitCoefficientEquiv G E V n).symm
    ((Finsupp.domLCongr (R := ℚ) (orbitEquiv p hp n)).symm
      (vertexCoefficientEquiv p hp V n (DFinsupp.single σ c))) = _
  rw [vertexCoefficientEquiv_single]
  simp only [Finsupp.domLCongr_symm, Finsupp.domLCongr_single]
  exact orbitCoefficientEquiv_symm_single G E V n ((orbitEquiv p hp n).symm σ) _

end TernaryPoly.SingularLocalHomology
