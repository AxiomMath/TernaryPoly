module

public import TernaryPeriodPolynomials.Topology.Covering.SingularOrbits

@[expose] public section


noncomputable section
namespace TernaryPoly.CoveringSingularOrbits
open CategoryTheory FreeActionLinearization
open scoped Simplicial
variable {G : Type} [Group G] {E B : TopCat} [MulAction G E] [ContinuousConstSMul G E]

/-- The actual covering fiber over a point. -/
def Fiber (p : E ⟶ B) (b : B) := {e : E // p e=b}

/-- The actual set of singular simplices lifting a fixed base simplex. -/
def Lifts (p : E ⟶ B) {n : ℕ} (σ : SingularSimplex B n) :=
  {τ : SingularSimplex E n // projection p n τ=σ}

/-- Evaluation at the chosen actual vertex of a singular simplex. -/
def atVertex {X : TopCat} {n : ℕ} (σ : SingularSimplex X n) : X :=
  TopCat.toSSetObjEquiv X (.op ⦋n⦌) σ (vertex n)

@[simp] theorem atVertex_projection (p : E ⟶ B) {n : ℕ} (τ : SingularSimplex E n) :
    atVertex (projection p n τ)=p (atVertex τ) := rfl

@[simp] theorem atVertex_smul {n : ℕ} (g : G) (τ : SingularSimplex E n) :
    atVertex (g • τ)=g • atVertex τ := by
  simp [atVertex]

/-- Evaluation sends an actual lift to the covering fiber at the base vertex. -/
def liftVertex (p : E ⟶ B) {n : ℕ} (σ : SingularSimplex B n) :
    Lifts p σ → Fiber p (atVertex σ) :=
  fun τ => ⟨atVertex τ.val,by rw [← atVertex_projection,τ.property]⟩

omit [ContinuousConstSMul G E] in
/-- A lift is determined by its value at the vertex. -/
theorem liftVertex_injective (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {n : ℕ} (σ : SingularSimplex B n) : Function.Injective (liftVertex p σ) := by
  intro τ υ h
  apply Subtype.ext
  apply (TopCat.toSSetObjEquiv E (.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  apply congrFun (hp.isCoveringMap.eq_of_comp_eq
    (TopCat.toSSetObjEquiv E (.op ⦋n⦌) τ.val).continuous
    (TopCat.toSSetObjEquiv E (.op ⦋n⦌) υ.val).continuous ?_ (vertex n)
    (congrArg Subtype.val h))
  exact congrArg (fun s => (TopCat.toSSetObjEquiv B (.op ⦋n⦌) s).toFun)
    (τ.property.trans υ.property.symm)

omit [ContinuousConstSMul G E] in
/-- Every point of the vertex fiber is the vertex of a unique simplex lift. -/
theorem liftVertex_surjective (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {n : ℕ} (σ : SingularSimplex B n) : Function.Surjective (liftVertex p σ) := by
  intro e
  let f := TopCat.toSSetObjEquiv B (.op ⦋n⦌) σ
  obtain ⟨F,⟨hF0,hF⟩,_⟩ := hp.isCoveringMap.existsUnique_continuousMap_lifts
    f (vertex n) e.val e.property
  have ht : projection p n ((TopCat.toSSetObjEquiv E (.op ⦋n⦌)).symm F)=σ := by
    apply (TopCat.toSSetObjEquiv B (.op ⦋n⦌)).injective
    rw [projection_equiv,Equiv.apply_symm_apply]
    exact ContinuousMap.ext (congrFun hF)
  refine ⟨⟨_,ht⟩,?_⟩
  apply Subtype.ext
  change TopCat.toSSetObjEquiv E (.op ⦋n⦌)
    ((TopCat.toSSetObjEquiv E (.op ⦋n⦌)).symm F) (vertex n)=e.val
  simpa only [Equiv.apply_symm_apply] using hF0

/-- The canonical actual lift/vertex-fiber equivalence. -/
def liftVertexEquiv (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {n : ℕ} (σ : SingularSimplex B n) : Lifts p σ ≃ Fiber p (atVertex σ) :=
  Equiv.ofBijective (liftVertex p σ)
    ⟨liftVertex_injective p hp σ,liftVertex_surjective p hp σ⟩

/-- The deck action restricted to the literal fiber. -/
def fiberSmul (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) {b : B}
    (g : G) (e : Fiber p b) : Fiber p b :=
  ⟨g • e.val,(hp.map_smul g).trans e.property⟩

/-- The deck action restricted to the literal lift set. -/
def liftsSmul (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) {n : ℕ}
    {σ : SingularSimplex B n} (g : G) (τ : Lifts p σ) : Lifts p σ :=
  ⟨g • τ.val,(projection_smul p hp n g τ.val).trans τ.property⟩

/-- The canonical lift/fiber bijection is equivariant for actual deck transformations. -/
theorem liftVertexEquiv_smul (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {n : ℕ} (σ : SingularSimplex B n) (g : G) (τ : Lifts p σ) :
    liftVertexEquiv p hp σ (liftsSmul p hp g τ)=
      fiberSmul p hp g (liftVertexEquiv p hp σ τ) := by
  apply Subtype.ext
  exact atVertex_smul g τ.val

/-- Equivariance in the lift-producing direction retains the same action convention. -/
theorem liftVertexEquiv_symm_smul (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {n : ℕ} (σ : SingularSimplex B n) (g : G) (e : Fiber p (atVertex σ)) :
    (liftVertexEquiv p hp σ).symm (fiberSmul p hp g e)=
      liftsSmul p hp g ((liftVertexEquiv p hp σ).symm e) := by
  apply (liftVertexEquiv p hp σ).injective
  rw [Equiv.apply_symm_apply,liftVertexEquiv_smul,Equiv.apply_symm_apply]

end TernaryPoly.CoveringSingularOrbits
