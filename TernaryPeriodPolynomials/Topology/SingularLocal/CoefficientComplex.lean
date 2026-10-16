module

public import TernaryPeriodPolynomials.Topology.SingularLocal.CoefficientAction
public import TernaryPeriodPolynomials.Topology.SingularLocal.CoefficientTransport

@[expose] public section


noncomputable section
open CategoryTheory Limits
open scoped Simplicial
namespace TernaryPoly.SingularLocalCoefficient
open FreeActionLinearization CoveringSingularOrbits EquivariantSingularResolution
open EquivariantSingularCohomology

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep.{0} ℚ G)

/-- A face coefficient is transported along the actual path inside the simplex to its first vertex. -/
def faceOperator (n : ℕ) (i : Fin (n+2)) :
    VertexCochain p hp V n →ₗ[ℚ] VertexCochain p hp V (n+1) where
  toFun c σ := coefficientTransportLinear p hp (simplexPullPath (simplexCoface n i) σ)
    (c (pullSimplex (simplexCoface n i) σ))
  map_add' c d := by
    funext σ
    exact map_add (coefficientTransportLinear p hp (simplexPullPath (simplexCoface n i) σ)) _ _
  map_smul' r c := by
    funext σ
    exact map_smul (coefficientTransportLinear p hp (simplexPullPath (simplexCoface n i) σ)) _ _

/-- The genuine geometric singular differential is the alternating sum of transported face coefficients. -/
def differential (n : ℕ) : VertexCochain p hp V n →ₗ[ℚ] VertexCochain p hp V (n+1) :=
  ∑ i : Fin (n+2), (-1 : ℤ)^i.val • faceOperator p hp V n i

omit [ContinuousConstSMul G E] in
/-- The differential is literally expressed using actual face simplices and actual local-system transport. -/
theorem differential_apply (n : ℕ) (c : VertexCochain p hp V n)
    (σ : SingularSimplex B (n+1)) :
    differential p hp V n c σ=
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        coefficientTransportLinear p hp (simplexPullPath (simplexCoface n i) σ)
          (c (pullSimplex (simplexCoface n i) σ)) := by
  simp only [differential,LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply]
  rfl

omit [ContinuousConstSMul G E] in
/-- Evaluating a transported face at the lifted vertex gives evaluation on the actual lifted face. -/
theorem faceOperator_vertexToFunction (n : ℕ) (i : Fin (n+2))
    (c : VertexCochain p hp V n) (τ : SingularSimplex E (n+1)) :
    vertexToFunction p hp (faceOperator p hp V n i c) τ=
      vertexToFunction p hp c ((TopCat.toSSet.obj E).δ i τ) := by
  have h := coefficient_simplexTransport p hp (simplexCoface n i) τ
    (c (pullSimplex (simplexCoface n i) (projection p (n+1) τ)))
  have h' := vertexToFunction_lift p hp c
    (⟨pullSimplex (simplexCoface n i) τ,projection_pullSimplex p (simplexCoface n i) τ⟩ :
      Lifts p (pullSimplex (simplexCoface n i) (projection p (n+1) τ)))
  exact h.trans h'.symm

omit [ContinuousConstSMul G E] in
/-- Lift evaluation intertwines the geometric differential and the actual alternating singular faces. -/
theorem differential_vertexToFunction (n : ℕ) (c : VertexCochain p hp V n)
    (τ : SingularSimplex E (n+1)) :
    vertexToFunction p hp (differential p hp V n c) τ=
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        vertexToFunction p hp c ((TopCat.toSSet.obj E).δ i τ) := by
  let ev : VertexCochain p hp V (n+1) →ₗ[ℚ] V :=
    (coefficientEvaluationLinearEquiv p hp
      (⟨atVertex τ,rfl⟩ : Fiber p (atVertex (projection p (n+1) τ)))) |>.toLinearMap.comp
        (LinearMap.proj (projection p (n+1) τ))
  change ev (differential p hp V n c)=_
  simp only [differential,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun v => (-1 : ℤ)^i.val • v) (faceOperator_vertexToFunction p hp V n i c τ)

/-- The actual Hom cochain differential agrees with the genuine transported-face differential. -/
theorem homVertexEquiv_d (n : ℕ) (f : chainRep G E n ⟶ V) :
    differential p hp V n (homVertexEquiv p hp V n f)=
      homVertexEquiv p hp V (n+1) ((cochains G E V).d n (n+1) f) := by
  apply (cochainVertexLinearEquiv (V := V) p hp (n+1)).symm.injective
  apply Subtype.ext
  funext τ
  change vertexToFunction p hp (differential p hp V n (homVertexEquiv p hp V n f)) τ=
    vertexToFunction p hp (homVertexEquiv p hp V (n+1) ((cochains G E V).d n (n+1) f)) τ
  refine (differential_vertexToFunction p hp V n (homVertexEquiv p hp V n f) τ).trans ?_
  refine Eq.trans ?_ ((evaluate_d G E V n f τ).symm.trans
    (vertexToFunction_homVertexEquiv p hp V (n+1) ((cochains G E V).d n (n+1) f) τ).symm)
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun v => (-1 : ℤ)^i.val • v)
    (vertexToFunction_homVertexEquiv p hp V n f _)

/-- The literal geometric differential squares to zero. -/
theorem differential_squared (n : ℕ) :
    (differential p hp V (n+1)).comp (differential p hp V n)=0 := by
  apply LinearMap.ext
  intro c
  obtain ⟨f,rfl⟩ := (homVertexEquiv p hp V n).surjective c
  change differential p hp V (n+1) (differential p hp V n (homVertexEquiv p hp V n f))=0
  have h := congrArg (fun u => u f) ((cochains G E V).d_comp_d n (n+1) (n+2))
  have hz : (cochains G E V).d (n+1) (n+2) ((cochains G E V).d n (n+1) f)=0 := h
  exact (congrArg (differential p hp V (n+1)) (homVertexEquiv_d p hp V n f)).trans
    ((homVertexEquiv_d p hp V (n+1) ((cochains G E V).d n (n+1) f)).trans
      ((congrArg (homVertexEquiv p hp V (n+2)) hz).trans (map_zero _)))

/-- The actual geometric local-coefficient singular cochain complex on the quotient base. -/
def localCochains : CochainComplex (ModuleCat ℚ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℚ (VertexCochain p hp V n))
    (fun n => ModuleCat.ofHom (differential p hp V n)) (fun n => by
      apply ModuleCat.hom_ext
      exact differential_squared p hp V n)

/-- The termwise actual fiber-coefficient correspondence is a genuine cochain isomorphism. -/
def cochainIso : cochains G E V ≅ localCochains p hp V :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (homVertexEquiv p hp V n).toModuleIso) (fun i j hij => by
      obtain rfl : j=i+1 := hij.symm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      simp only [localCochains,CochainComplex.of_d]
      convert homVertexEquiv_d p hp V i f using 1 <;> rfl)

end TernaryPoly.SingularLocalCoefficient
