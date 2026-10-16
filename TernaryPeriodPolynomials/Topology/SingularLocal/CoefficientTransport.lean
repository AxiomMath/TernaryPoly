module

public import TernaryPeriodPolynomials.Topology.Covering.SimplexTransport
public import TernaryPeriodPolynomials.Topology.Covering.CoefficientModule

@[expose] public section

noncomputable section
open CategoryTheory
open scoped Simplicial
namespace TernaryPoly.SingularLocalCoefficient
open FreeActionLinearization CoveringSingularOrbits

variable {G : Type} [Group G] {E B : TopCat} [MulAction G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)

/-- Changing displayed endpoints of a path leaves the lifted endpoint value unchanged. -/
theorem fiberTransport_cast_val {x y x' y' : B}
    (γ : Path.Homotopic.Quotient x y) (hx : x'=x) (hy : y'=y) (e : Fiber p x') :
    (fiberTransport p hp (γ.cast hx hy) e).val=
      (fiberTransport p hp γ ⟨e.val,e.property.trans hx⟩).val := by
  cases hx
  cases hy
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]
  rfl

/-- Actual simplex-path transport sends the reparametrized lift vertex to the original lift vertex. -/
theorem simplexTransport_projected {m n : ℕ}
    (θ : C(Convexity.StdSimplex ℝ (Fin (m+1)),Convexity.StdSimplex ℝ (Fin (n+1))))
    (τ : SingularSimplex E n) :
    fiberTransport p hp (simplexPullPath θ (projection p n τ))
      (⟨atVertex (pullSimplex θ τ),by
        rw [←atVertex_projection,projection_pullSimplex]⟩ :
        Fiber p (atVertex (pullSimplex θ (projection p n τ))))=
      ⟨atVertex τ,rfl⟩ := by
  apply Subtype.ext
  refine (fiberTransport_cast_val p hp
    ((simplexPath (θ (vertex m)) (vertex n)).map
      (TopCat.toSSetObjEquiv B (.op ⦋n⦌) (projection p n τ)))
    (atVertex_pullSimplex θ (projection p n τ)) rfl
    ⟨atVertex (pullSimplex θ τ),by rw [←atVertex_projection,projection_pullSimplex]⟩).trans ?_
  simpa only [projection_equiv,atVertex,pullSimplex_equiv,ContinuousMap.comp_apply] using
    congrArg Subtype.val (fiberTransport_projected_path p hp
      (TopCat.toSSetObjEquiv E (.op ⦋n⦌) τ) (simplexPath (θ (vertex m)) (vertex n)))

/-- Literal coefficient transport along the simplex path preserves values at the lifted vertices. -/
theorem coefficient_simplexTransport {V : Type*} [MulAction G V] {m n : ℕ}
    (θ : C(Convexity.StdSimplex ℝ (Fin (m+1)),Convexity.StdSimplex ℝ (Fin (n+1))))
    (τ : SingularSimplex E n)
    (c : FiberCoefficient p hp V (atVertex (pullSimplex θ (projection p n τ)))) :
    (coefficientTransport p hp (simplexPullPath θ (projection p n τ)) c).val
      ⟨atVertex τ,rfl⟩=
    c.val ⟨atVertex (pullSimplex θ τ),by
      rw [←atVertex_projection,projection_pullSimplex]⟩ := by
  have h := coefficientTransport_apply_transport p hp
    (simplexPullPath θ (projection p n τ)) c
    ⟨atVertex (pullSimplex θ τ),by rw [←atVertex_projection,projection_pullSimplex]⟩
  rw [simplexTransport_projected] at h
  exact h

end TernaryPoly.SingularLocalCoefficient
