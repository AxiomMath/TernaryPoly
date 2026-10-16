module

public import TernaryPeriodPolynomials.Topology.CoverGroup.GroupReindexFibers

@[expose] public section

/-! Group reindexing preserves the literal transported-face singular differential. -/
noncomputable section
namespace TernaryPoly.CoverGroupReindex
open CategoryTheory HomologicalComplex CoveringSingularOrbits SingularLocalCoefficient

variable {G H : Type} [Group G] [Group H] (e : H ≃* G)
  {E B : TopCat.{0}} [MulAction H E] [MulAction G E]
  (p : E ⟶ B) (hH : IsQuotientCoveringMap p H) (hG : IsQuotientCoveringMap p G)
  (hact : ∀ (h : H) (x : E), h • x = e h • x) (V : Rep.{0} ℚ G)

def vertexEquiv (n : ℕ) : VertexCochain p hG V n ≃ₗ[ℚ]
    VertexCochain p hH (Rep.res e.toMonoidHom V) n :=
  LinearEquiv.piCongrRight (fun σ => coefficientEquiv e p hH hG hact V (atVertex σ))

@[simp] theorem vertexEquiv_apply (n : ℕ) (c : VertexCochain p hG V n)
    (σ : FreeActionLinearization.SingularSimplex B n) (z : Fiber p (atVertex σ)) :
    (vertexEquiv e p hH hG hact V n c σ).val z = (c σ).val z := rfl

theorem vertexEquiv_differential (n : ℕ) (c : VertexCochain p hG V n) :
    vertexEquiv e p hH hG hact V (n+1) (differential p hG V n c) =
      differential p hH (Rep.res e.toMonoidHom V) n (vertexEquiv e p hH hG hact V n c) := by
  funext σ
  change coefficientEquiv e p hH hG hact V (atVertex σ) (differential p hG V n c σ) = _
  rw [differential_apply, differential_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  rfl

variable [ContinuousConstSMul H E] [ContinuousConstSMul G E]

/-- The map is a genuine isomorphism of the existing geometric local-cochain complexes. -/
def cochainIso : localCochains p hG V ≅ localCochains p hH (Rep.res e.toMonoidHom V) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (vertexEquiv e p hH hG hact V n).toModuleIso) (fun i j hij => by
      obtain rfl : j = i + 1 := hij.symm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      simp only [localCochains, CochainComplex.of_d]
      convert (vertexEquiv_differential e p hH hG hact V i c).symm using 1 <;> rfl)

end TernaryPoly.CoverGroupReindex
