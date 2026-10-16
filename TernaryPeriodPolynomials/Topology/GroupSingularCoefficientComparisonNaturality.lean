module

public import TernaryPeriodPolynomials.Topology.GroupSingularCoefficientComparison

@[expose] public section


noncomputable section
open CategoryTheory HomologicalComplex
namespace TernaryPoly.SingularLocalCoefficient
open CoveringSingularOrbits FreeActionLinearization EquivariantSingularResolution

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)

/-- A representation morphism acts pointwise on the actual covering-fiber coefficient module. -/
def coefficientMap {V W : Rep.{0} ℚ G} (φ : V ⟶ W) (b : B) :
    FiberCoefficient p hp V b →ₗ[ℚ] FiberCoefficient p hp W b where
  toFun c := ⟨fun e => φ.hom (c.val e),fun g e =>
    (congrArg (fun v => φ.hom v) (c.property g e)).trans
      (congrArg (fun l => l (c.val e)) (φ.hom.isIntertwining' g))⟩
  map_add' c d := by apply Subtype.ext; funext e; exact map_add _ _ _
  map_smul' r c := by apply Subtype.ext; funext e; exact map_smul _ _ _

omit [ContinuousConstSMul G E] in
/-- Actual coefficient maps commute with actual path-lift transport. -/
theorem coefficientMap_transport {V W : Rep.{0} ℚ G} (φ : V ⟶ W) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (c : FiberCoefficient p hp V x) :
    coefficientMap p hp φ y (coefficientTransportLinear p hp γ c)=
      coefficientTransportLinear p hp γ (coefficientMap p hp φ x c) := rfl

/-- Coefficient morphisms give genuine natural transformations of the actual rational local systems. -/
def localSystemMap {V W : Rep.{0} ℚ G} (φ : V ⟶ W) :
    coefficientLocalSystem (V := V) p hp ⟶ coefficientLocalSystem (V := W) p hp where
  app b := ModuleCat.ofHom (coefficientMap p hp φ b.as)
  naturality _ _ γ := by ext c; rfl

/-- Pointwise coefficient maps on the literal base-simplex vertex assignments. -/
def vertexMap {V W : Rep.{0} ℚ G} (φ : V ⟶ W) (n : ℕ) :
    VertexCochain p hp V n →ₗ[ℚ] VertexCochain p hp W n where
  toFun c σ := coefficientMap p hp φ (atVertex σ) (c σ)
  map_add' c d := by funext σ; exact map_add (coefficientMap p hp φ (atVertex σ)) _ _
  map_smul' r c := by funext σ; exact map_smul (coefficientMap p hp φ (atVertex σ)) _ _

omit [ContinuousConstSMul G E] in
/-- The actual transported face operator is natural in the coefficients. -/
theorem faceOperator_natural {V W : Rep.{0} ℚ G} (φ : V ⟶ W) (n : ℕ) (i : Fin (n+2))
    (c : VertexCochain p hp V n) :
    vertexMap p hp φ (n+1) (faceOperator p hp V n i c)=
      faceOperator p hp W n i (vertexMap p hp φ n c) := rfl

omit [ContinuousConstSMul G E] in
/-- The literal geometric alternating differential commutes with coefficient maps. -/
theorem differential_natural {V W : Rep.{0} ℚ G} (φ : V ⟶ W) (n : ℕ)
    (c : VertexCochain p hp V n) :
    vertexMap p hp φ (n+1) (differential p hp V n c)=
      differential p hp W n (vertexMap p hp φ n c) := by
  simp only [differential,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun v => (-1 : ℤ)^i.val • v) (faceOperator_natural p hp φ n i c)

/-- The actual coefficient map on the geometric local-system singular cochain complexes. -/
def localCochainMap {V W : Rep.{0} ℚ G} (φ : V ⟶ W) :
    localCochains p hp V ⟶ localCochains p hp W where
  f n := ModuleCat.ofHom (vertexMap p hp φ n)
  comm' i j hij := by
    obtain rfl : j=i+1 := hij.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    simp only [localCochains,CochainComplex.of_d]
    convert (differential_natural p hp φ i c).symm using 1

/-- The literal fiber-coefficient cochain correspondence commutes with representation morphisms. -/
theorem homVertexEquiv_natural {V W : Rep.{0} ℚ G} (φ : V ⟶ W) (n : ℕ)
    (f : chainRep G E n ⟶ V) :
    homVertexEquiv p hp W n (f ≫ φ)=vertexMap p hp φ n (homVertexEquiv p hp V n f) := rfl

/-- The genuine geometric cochain isomorphism is natural in its coefficients. -/
theorem cochainIso_natural {V W : Rep.{0} ℚ G} (φ : V ⟶ W) :
    EquivariantSingularCohomology.cochainMap G E φ ≫ (cochainIso p hp W).hom=
      (cochainIso p hp V).hom ≫ localCochainMap p hp φ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact homVertexEquiv_natural p hp φ n f

variable [ContractibleSpace E] [IsCancelSMul G E]

/-- Actual group-cohomology coefficient maps match the geometric local-system coefficient maps. -/
theorem groupLocalCohomologyIso_natural {V W : Rep.{0} ℚ G} (φ : V ⟶ W) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) φ n ≫ (groupLocalCohomologyIso p hp W n).hom=
      (groupLocalCohomologyIso p hp V n).hom ≫ homologyMap (localCochainMap p hp φ) n := by
  change groupCohomology.map (MonoidHom.id G) φ n ≫
      ((EquivariantSingularCohomology.groupCohomologyIso G E W n).hom ≫
        homologyMap (cochainIso p hp W).hom n)=
    ((EquivariantSingularCohomology.groupCohomologyIso G E V n).hom ≫
      homologyMap (cochainIso p hp V).hom n) ≫ homologyMap (localCochainMap p hp φ) n
  rw [←Category.assoc,EquivariantSingularCohomology.groupCohomologyIso_natural,Category.assoc,
    ←homologyMap_comp,cochainIso_natural,homologyMap_comp,←Category.assoc]

end TernaryPoly.SingularLocalCoefficient
