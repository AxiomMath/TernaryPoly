module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Complex

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalHomology
open CategoryTheory FreeActionLinearization CoveringSingularOrbits EquivariantSingularResolution
open scoped Classical

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
variable {V W : Rep.{0} ℚ G}

/-- An equivariant coefficient morphism acts on actual fiber coefficients by literal postcomposition. -/
def fiberCoefficientMap (φ : V ⟶ W) (b : B) :
    FiberCoefficient p hp V b →ₗ[ℚ] FiberCoefficient p hp W b where
  toFun c := ⟨fun e => φ (c.val e), fun g e =>
    (congrArg φ (c.property g e)).trans
      (congrArg (fun f => f (c.val e)) (φ.hom.isIntertwining' g))⟩
  map_add' c d := by apply Subtype.ext; funext e; exact map_add φ.hom.toLinearMap _ _
  map_smul' r c := by apply Subtype.ext; funext e; exact map_smul φ.hom.toLinearMap r _

/-- Fiber coefficient maps commute with the actual path-lift transport. -/
theorem fiberCoefficientMap_transport (φ : V ⟶ W) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (c : FiberCoefficient p hp V x) :
    fiberCoefficientMap p hp φ y (coefficientTransportLinear p hp γ c) =
      coefficientTransportLinear p hp γ (fiberCoefficientMap p hp φ x c) := rfl

/-- The genuine degreewise coefficient map acts componentwise on the dependent finite direct sum. -/
def vertexCoefficientMap (φ : V ⟶ W) (n : ℕ) :
    VertexChain p hp V n →ₗ[ℚ] VertexChain p hp W n :=
  DFinsupp.mapRange.linearMap (fun σ => fiberCoefficientMap p hp φ (atVertex σ))

/-- The coefficient map preserves each actual simplex index. -/
theorem vertexCoefficientMap_single (φ : V ⟶ W) (n : ℕ) (σ : SingularSimplex B n)
    (c : FiberCoefficient p hp V (atVertex σ)) :
    vertexCoefficientMap p hp φ n (DFinsupp.single σ c) =
      DFinsupp.single σ (fiberCoefficientMap p hp φ (atVertex σ) c) := by
  simp [vertexCoefficientMap]

variable [ContinuousConstSMul G E]

/-- The actual tensor-coinvariant coefficient map is the natural transformation of its first variable. -/
def coinvariantCoefficientMap (φ : V ⟶ W) :
    coinvariantChains G E V ⟶ coinvariantChains G E W where
  f n := ((Rep.coinvariantsTensor ℚ G).map φ).app (chainRep G E n)
  comm' i j _ := (((Rep.coinvariantsTensor ℚ G).map φ).naturality (equivariantD G E i j)).symm

/-- Tensor-coinvariant coefficient maps act literally on the first tensor coordinate. -/
theorem tensorCoinvariant_coefficient_mk (φ : V ⟶ W) (A : Rep ℚ G) (v : V) (a : A) :
    (((Rep.coinvariantsTensor ℚ G).map φ).app A) (Rep.coinvariantsTensorMk V A v a) =
      Rep.coinvariantsTensorMk W A (φ v) a := rfl

/-- The actual singular coinvariant coefficient map retains the simplex and applies φ to its value. -/
theorem coinvariantCoefficientMap_generator (φ : V ⟶ W) (n : ℕ)
    (τ : SingularSimplex E n) (v : V) :
    (coinvariantCoefficientMap (E := E) φ).f n (generator G E V n τ v) =
      generator G E W n τ (φ v) := rfl

variable [IsCancelSMul G E]

/-- The genuine chain-level coefficient map between geometric local-coefficient chain complexes. -/
def localCoefficientMap (φ : V ⟶ W) : localChains p hp V ⟶ localChains p hp W :=
  (chainIso p hp V).inv ≫ coinvariantCoefficientMap (E := E) φ ≫ (chainIso p hp W).hom

/-- The chain map just defined acts literally by the actual fiber-coefficient morphism. -/
theorem localCoefficientMap_single (φ : V ⟶ W) (n : ℕ) (σ : SingularSimplex B n)
    (c : FiberCoefficient p hp V (atVertex σ)) :
    (localCoefficientMap p hp φ).f n (DFinsupp.single σ c) =
      DFinsupp.single σ (fiberCoefficientMap p hp φ (atVertex σ) c) := by
  apply (degreeEquiv p hp W n).symm.injective
  change (degreeEquiv p hp W n).symm ((degreeEquiv p hp W n)
    ((coinvariantCoefficientMap (E := E) φ).f n
      ((degreeEquiv p hp V n).symm (DFinsupp.single σ c)))) = _
  rw [LinearEquiv.symm_apply_apply, degreeEquiv_symm_single_lift p hp V n (chosenLift p hp n σ),
    degreeEquiv_symm_single_lift p hp W n (chosenLift p hp n σ), coinvariantCoefficientMap_generator]
  rfl

/-- The entire degree map is the componentwise map of the actual dependent finite direct sum. -/
theorem localCoefficientMap_f (φ : V ⟶ W) (n : ℕ) :
    ((localCoefficientMap p hp φ).f n).hom = vertexCoefficientMap p hp φ n := by
  apply DFinsupp.lhom_ext
  intro σ c
  exact (localCoefficientMap_single p hp φ n σ c).trans
    (vertexCoefficientMap_single p hp φ n σ c).symm

/-- The actual degreewise geometric chain isomorphism is natural in all coefficient morphisms. -/
theorem chainIso_coefficient_natural (φ : V ⟶ W) :
    (chainIso p hp V).hom ≫ localCoefficientMap p hp φ =
      coinvariantCoefficientMap (E := E) φ ≫ (chainIso p hp W).hom := by
  simp [localCoefficientMap]

end TernaryPoly.SingularLocalHomology
