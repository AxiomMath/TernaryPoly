module

public import TernaryPeriodPolynomials.GroupCohomology.FreeAction.ActionLinearizationSingular
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison
public import Mathlib.Algebra.Category.ModuleCat.Colimits

@[expose] public section


noncomputable section
open CategoryTheory Limits AlgebraicTopology
open scoped Simplicial
namespace TernaryPoly.SmoothSingularGlobal
open FreeActionLinearization

variable (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X] [ContinuousConstSMul G X]

/-- The underlying complex is literally Mathlib's real singular chain complex. -/
abbrev underlyingChains : ChainComplex (ModuleCat ℝ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat ℝ)).obj (ModuleCat.of ℝ ℝ)).obj X

/-- The actual singular chain map induced by the continuous scalar action. -/
def scalarChainMap (g : G) : underlyingChains X ⟶ underlyingChains X :=
  ((singularChainComplexFunctor (ModuleCat ℝ)).obj (ModuleCat.of ℝ ℝ)).map (scalarMap G X g)

@[simp] theorem scalarMap_one : scalarMap G X 1=𝟙 X := by
  ext x
  exact one_smul G x

theorem scalarMap_mul (g h : G) : scalarMap G X (g*h)=scalarMap G X h ≫ scalarMap G X g := by
  ext x
  exact mul_smul g h x

@[simp] theorem scalarChainMap_one : scalarChainMap G X 1=𝟙 (underlyingChains X) := by
  rw [scalarChainMap,scalarMap_one,CategoryTheory.Functor.map_id]

theorem scalarChainMap_mul (g h : G) :
    scalarChainMap G X (g*h)=scalarChainMap G X h ≫ scalarChainMap G X g := by
  rw [scalarChainMap,scalarMap_mul,CategoryTheory.Functor.map_comp]
  rfl

/-- The actual induced action on degree-n singular chains. -/
def chainAction (n : ℕ) : Representation ℝ G ((underlyingChains X).X n) where
  toFun g := ((scalarChainMap G X g).f n).hom
  map_one' := by
    rw [scalarChainMap_one]
    rfl
  map_mul' g h := by
    rw [scalarChainMap_mul]
    rfl

abbrev chainRep (n : ℕ) : Rep ℝ G := Rep.of (chainAction G X n)

/-- Singular differentials are equivariant because the action is induced by actual chain maps. -/
def equivariantD (i j : ℕ) : chainRep G X i ⟶ chainRep G X j :=
  Rep.ofHom ⟨((underlyingChains X).d i j).hom,fun g =>
    congrArg ModuleCat.Hom.hom ((scalarChainMap G X g).comm i j)⟩

/-- The genuine singular chain complex, carrying its induced representation in each degree. -/
def equivariantChains : ChainComplex (Rep ℝ G) ℕ where
  X := chainRep G X
  d := equivariantD G X
  shape i j hij := by
    ext x
    exact congrArg (fun u => u x) ((underlyingChains X).shape i j hij)
  d_comp_d' i j k _ _ := by
    ext x
    exact congrArg (fun u => u x) ((underlyingChains X).d_comp_d i j k)

/-- Forgetting the action leaves the literal singular chain modules and differential unchanged. -/
def forgetChainIso :
    ((forget₂ (Rep ℝ G) (ModuleCat ℝ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (equivariantChains G X) ≅ underlyingChains X :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => by rfl)

/-- The actual generator formula identifies the differential as the alternating face sum. -/
theorem generator_d (n : ℕ) (σ : SingularSimplex X (n+1)) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ ((forget₂ (Rep ℝ G) (ModuleCat ℝ)).map
      (equivariantD G X (n+1) n)) =
      ∑ i : Fin (n+2),(-1 : ℤ)^i.val • (TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).δ i σ) :=
  (TopCat.toSSet.obj X).ιChainComplex_d (R := ModuleCat.of ℝ ℝ) σ

/-- Scalar action sends each actual singular generator to its acted-upon singular simplex. -/
theorem generator_smul (n : ℕ) (σ : SingularSimplex X n) (g : G) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ (scalarChainMap G X g).f n=
      (TopCat.toSSet.obj X).ιChainComplex (g • σ) := by
  rw [singular_smul_eq_map]
  exact SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map (scalarMap G X g))
    (ModuleCat.of ℝ ℝ) σ

end TernaryPoly.SmoothSingularGlobal
