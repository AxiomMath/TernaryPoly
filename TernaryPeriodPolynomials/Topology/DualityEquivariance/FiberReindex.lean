module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.RelativeLeibniz

@[expose] public section


/-!
# Reindexing the coefficients of two coverings of the same base

Two quotient coverings `p`, `q` of the same base with the same group and coefficient representation
carry fibre coefficient systems.  A `FiberReindex` is a family of linear maps between the fibre
coefficients commuting with the covering transport along paths.  It induces a map of geometric local
cochains (a cochain map), a map of geometric local chains, and the cap product is natural for it
(`FiberReindex.cap`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.DualityEquivariance

open CategoryTheory TernaryPoly TernaryPoly.CoveringSingularOrbits
  TernaryPoly.SingularLocalCoefficient TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap
  TernaryPoly.FreeActionLinearization SphereOddDegree.AffineBarycentricSubdivision
  SphereOddDegree.AlexanderWhitney

section Generic

variable {G : Type} [Group G] {E E' B : TopCat.{0}} [MulAction G E] [MulAction G E']
  [ContinuousConstSMul G E] [ContinuousConstSMul G E']
  (p : E ⟶ B) (q : E' ⟶ B) (hp : IsQuotientCoveringMap p G) (hq : IsQuotientCoveringMap q G)
  (V : Rep.{0} ℚ G)

/-- A family of coefficient maps between the fibre coefficient systems of two coverings of the same
base, commuting with the transport along paths. -/
structure FiberReindex where
  ε : ∀ b : B, FiberCoefficient p hp V b →ₗ[ℚ] FiberCoefficient q hq V b
  transport : ∀ {x y : B} (γ : Path.Homotopic.Quotient x y) (c : FiberCoefficient p hp V x),
    ε y (coefficientTransportLinear p hp γ c) = coefficientTransportLinear q hq γ (ε x c)

variable {p q hp hq V} (R : FiberReindex p q hp hq V)

/-- Reindexing of cochains. -/
def FiberReindex.cochain (a : ℕ) : VertexCochain p hp V a →ₗ[ℚ] VertexCochain q hq V a where
  toFun φ σ := R.ε _ (φ σ)
  map_add' φ ψ := funext fun σ => map_add _ _ _
  map_smul' r φ := funext fun σ => by simp [map_smul]

/-- Reindexing of chains. -/
def FiberReindex.chain (b : ℕ) : VertexChain p hp V b →ₗ[ℚ] VertexChain q hq V b :=
  DFinsupp.mapRange.linearMap (fun σ => R.ε (atVertex σ))

omit [ContinuousConstSMul G E] [ContinuousConstSMul G E'] in
theorem FiberReindex.chain_single (b : ℕ) (σ : SingularSimplex B b)
    (c : FiberCoefficient p hp V (atVertex σ)) :
    FiberReindex.chain R b (DFinsupp.single σ c) = DFinsupp.single σ (R.ε _ c) := by
  unfold FiberReindex.chain
  simp [DFinsupp.mapRange_single]

omit [ContinuousConstSMul G E] [ContinuousConstSMul G E'] in
/-- A linear map of chains that acts on generators as the reindexing is the reindexing. -/
theorem FiberReindex.chain_unique (b : ℕ) (L : VertexChain p hp V b →ₗ[ℚ] VertexChain q hq V b)
    (h : ∀ (σ : SingularSimplex B b) (c : FiberCoefficient p hp V (atVertex σ)),
      L (DFinsupp.single σ c) = DFinsupp.single σ (R.ε _ c)) :
    L = FiberReindex.chain R b :=
  DFinsupp.lhom_ext fun σ c => (h σ c).trans (FiberReindex.chain_single R b σ c).symm

omit [ContinuousConstSMul G E] [ContinuousConstSMul G E'] in
theorem FiberReindex.cochain_apply (a : ℕ) (φ : VertexCochain p hp V a) (σ : SingularSimplex B a) :
    FiberReindex.cochain R a φ σ = R.ε _ (φ σ) := rfl

omit [ContinuousConstSMul G E] [ContinuousConstSMul G E'] in
theorem FiberReindex.cochain_differential (a : ℕ) (φ : VertexCochain p hp V a) :
    FiberReindex.cochain R (a + 1) (differential p hp V a φ) =
      differential q hq V a (FiberReindex.cochain R a φ) := by
  funext σ
  rw [FiberReindex.cochain_apply, differential_apply, differential_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, R.transport]
  rfl

/-- The reindexing as a cochain map of the geometric local cochain complexes. -/
def FiberReindex.cochainMap : localCochains p hp V ⟶ localCochains q hq V where
  f n := ModuleCat.ofHom (FiberReindex.cochain R n)
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    simp only [localCochains, CochainComplex.of_d]
    exact (FiberReindex.cochain_differential R i c).symm

omit [ContinuousConstSMul G E] [ContinuousConstSMul G E'] in
theorem FiberReindex.capSimplex (a b : ℕ) (σ : SingularSimplex B (a + b))
    (φ : VertexCochain p hp V a) :
    SingularLocalCap.capSimplex q hq V a b σ (FiberReindex.cochain R a φ) =
      FiberReindex.chain R b (SingularLocalCap.capSimplex p hp V a b σ φ) := by
  rw [SingularLocalCap.capSimplex_apply, SingularLocalCap.capSimplex_apply]
  refine Eq.trans ?_ (FiberReindex.chain_single R b _ _).symm
  congr 1
  exact (congrArg (coefficientTransportLinear q hq _)
    (R.transport (simplexPullPath (frontMap a b) σ) _).symm).trans
    (R.transport (simplexPullPath (backMap a b) σ).symm _).symm

omit [ContinuousConstSMul G E] [ContinuousConstSMul G E'] in
theorem FiberReindex.cap (a b : ℕ) (φ : VertexCochain p hp V a)
    (c : singularChainGroup ℚ B (a + b)) :
    SingularLocalCap.cap q hq V a b (FiberReindex.cochain R a φ) c =
      FiberReindex.chain R b (SingularLocalCap.cap p hp V a b φ c) := by
  have : (SingularLocalCap.cap q hq V a b (FiberReindex.cochain R a φ)) =
      (FiberReindex.chain R b).comp (SingularLocalCap.cap p hp V a b φ) := by
    apply SingularLocalCap.scalarChain_ext
    intro σ
    simp only [SingularLocalCap.cap_generator, LinearMap.comp_apply, FiberReindex.capSimplex R]
  exact LinearMap.congr_fun this c

end Generic

end TernaryPeriodPolynomials.Argument.DualityEquivariance
