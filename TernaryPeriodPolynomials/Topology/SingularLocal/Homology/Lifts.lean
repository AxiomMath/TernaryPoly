module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Degrees
public import TernaryPeriodPolynomials.Topology.SingularLocal.CoefficientTransport

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalHomology
open scoped Classical
open CategoryTheory FreeActionLinearization CoveringSingularOrbits

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  [IsCancelSMul G E] (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep ℚ G)

/-- The inverse degree identification can be evaluated using any actual lift. Its tensor class
is independent of the chosen representative because coefficients transform diagonally. -/
theorem degreeEquiv_symm_single_lift (n : ℕ) {σ : SingularSimplex B n}
    (τ : Lifts p σ) (c : FiberCoefficient p hp V (atVertex σ)) :
    (degreeEquiv p hp V n).symm (DFinsupp.single σ c) =
      generator G E V n τ.val (c.val (liftVertexEquiv p hp σ τ)) := by
  obtain ⟨g, hg⟩ := (projection_eq_iff_orbit p hp n τ.val (chosenLift p hp n σ).val).mp
    (τ.property.trans (chosenLift p hp n σ).property.symm)
  have ht : liftsSmul p hp g (chosenLift p hp n σ) = τ := Subtype.ext hg
  have hv : c.val (liftVertexEquiv p hp σ τ) =
      V.ρ g (chosenEvaluation p hp V n σ c) := by
    rw [← ht, liftVertexEquiv_smul]
    exact c.property g _
  rw [degreeEquiv_symm_single, hv, ← hg]
  exact (generator_diagonal G E V n g (chosenLift p hp n σ).val
    (chosenEvaluation p hp V n σ c)).symm

/-- In the projected-simplex presentation, arbitrary-lift evaluation uses exactly its first vertex. -/
theorem degreeEquiv_symm_single_projected (n : ℕ) (τ : SingularSimplex E n)
    (c : FiberCoefficient p hp V (atVertex (projection p n τ))) :
    (degreeEquiv p hp V n).symm (DFinsupp.single (projection p n τ) c) =
      generator G E V n τ (c.val ⟨atVertex τ, rfl⟩) :=
  degreeEquiv_symm_single_lift p hp V n ⟨τ, rfl⟩ c

end TernaryPoly.SingularLocalHomology
