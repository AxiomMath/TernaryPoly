module

public import TernaryPeriodPolynomials.Topology.Covering.CoefficientTransport

@[expose] public section


noncomputable section
namespace TernaryPoly.CoveringSingularOrbits
open CategoryTheory FreeActionLinearization
open scoped Simplicial
variable {G : Type} [Group G] {E B : TopCat} [MulAction G E]

/-- Actual covering transport follows the endpoints of every projected path upstairs. -/
theorem fiberTransport_projected_path (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {A : Type*} [TopologicalSpace A] (F : C(A,E)) {a b : A}
    (γ : Path.Homotopic.Quotient a b) :
    fiberTransport p hp (γ.map (p.hom.comp F))
      (⟨F a,rfl⟩ : Fiber p (p (F a)))=⟨F b,rfl⟩ := by
  change hp.isCoveringMap.monodromy (γ.map (p.hom.comp F)) ⟨F a,rfl⟩=⟨F b,rfl⟩
  rw [Path.Homotopic.Quotient.map_comp]
  convert hp.isCoveringMap.monodromy_map (γ.map F) using 1

/-- Reparametrization of a literal Mathlib singular simplex by an actual continuous simplex map. -/
def pullSimplex {X : TopCat} {m n : ℕ}
    (θ : C(Convexity.StdSimplex ℝ (Fin (m+1)),Convexity.StdSimplex ℝ (Fin (n+1))))
    (σ : SingularSimplex X n) : SingularSimplex X m :=
  (TopCat.toSSetObjEquiv X (.op ⦋m⦌)).symm
    ((TopCat.toSSetObjEquiv X (.op ⦋n⦌) σ).comp θ)

@[simp] theorem pullSimplex_equiv {X : TopCat} {m n : ℕ}
    (θ : C(Convexity.StdSimplex ℝ (Fin (m+1)),Convexity.StdSimplex ℝ (Fin (n+1))))
    (σ : SingularSimplex X n) :
    TopCat.toSSetObjEquiv X (.op ⦋m⦌) (pullSimplex θ σ)=
      (TopCat.toSSetObjEquiv X (.op ⦋n⦌) σ).comp θ := Equiv.apply_symm_apply _ _

@[simp] theorem atVertex_pullSimplex {X : TopCat} {m n : ℕ}
    (θ : C(Convexity.StdSimplex ℝ (Fin (m+1)),Convexity.StdSimplex ℝ (Fin (n+1))))
    (σ : SingularSimplex X n) :
    atVertex (pullSimplex θ σ)=TopCat.toSSetObjEquiv X (.op ⦋n⦌) σ (θ (vertex m)) := by
  simp [atVertex]

/-- The actual projected reparametrized simplex is the reparametrized base simplex. -/
theorem projection_pullSimplex (p : E ⟶ B) {m n : ℕ}
    (θ : C(Convexity.StdSimplex ℝ (Fin (m+1)),Convexity.StdSimplex ℝ (Fin (n+1))))
    (τ : SingularSimplex E n) :
    projection p m (pullSimplex θ τ)=pullSimplex θ (projection p n τ) := by
  apply (TopCat.toSSetObjEquiv B (.op ⦋m⦌)).injective
  simp only [projection_equiv,pullSimplex_equiv]
  rfl

/-- The unique homotopy class connecting two points in the actual topological simplex. -/
def simplexPath {n : ℕ} (a b : Convexity.StdSimplex ℝ (Fin (n+1))) : Path.Homotopic.Quotient a b :=
  .mk (PathConnectedSpace.somePath a b)

/-- The local-system path from a reparametrized simplex vertex to the original vertex. -/
def simplexPullPath {X : TopCat} {m n : ℕ}
    (θ : C(Convexity.StdSimplex ℝ (Fin (m+1)),Convexity.StdSimplex ℝ (Fin (n+1))))
    (σ : SingularSimplex X n) :
    Path.Homotopic.Quotient (atVertex (pullSimplex θ σ)) (atVertex σ) :=
  ((simplexPath (θ (vertex m)) (vertex n)).map
    (TopCat.toSSetObjEquiv X (.op ⦋n⦌) σ)).cast
      (atVertex_pullSimplex θ σ).symm rfl

/-- The genuine topological coface map between standard simplices. -/
def simplexCoface (n : ℕ) (i : Fin (n+2)) :
    C(Convexity.StdSimplex ℝ (Fin (n+1)),Convexity.StdSimplex ℝ (Fin (n+2))) :=
  (SimplexCategory.toTop₀.map (SimplexCategory.δ i)).hom

/-- Pullback along this topological coface is literally Mathlib's singular face map. -/
theorem pullSimplex_coface {X : TopCat} (n : ℕ) (i : Fin (n+2))
    (σ : SingularSimplex X (n+1)) :
    pullSimplex (simplexCoface n i) σ=(TopCat.toSSet.obj X).δ i σ := rfl

end TernaryPoly.CoveringSingularOrbits
