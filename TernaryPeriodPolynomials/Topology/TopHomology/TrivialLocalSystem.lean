module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Augmentation

@[expose] public section


/-!
# Trivial local systems on a free quotient covering are ordinary singular chains

For a quotient covering `p : E ⟶ B` with deck group `G` (`IsQuotientCoveringMap p G`) and a rational
representation `V` of `G` on which `G` acts trivially, the local-coefficient singular chains of the
covering (`TernaryPoly.SingularLocalHomology.localChains p hp V`) are isomorphic, by evaluation at a chosen
point of each fiber, to Mathlib's singular chains of the base `B` with coefficients `ModuleCat.of ℚ V`:

* `coeff_const`: a fiber coefficient of a trivial representation is constant on each fiber;
* `fiberEquivT`, `fiberEquivT_transport`: fiber evaluation identifies the fiber coefficients with `V`,
  compatibly with every parallel transport;
* `trivialLocalChainIso`: the chain isomorphism (the identity-cover case is
  `TernaryPoly.SingularLocalConstant.ordinaryChainIso`; this is the same construction for an arbitrary
  covering);
* `trivialLocalH0Iso`: on a path-connected base, `H₀` of the trivial local system is `V`.

Reusable: nothing here is specific to the arithmetic boundary.

Formalized by Claude Sonnet 5.5.
-/


open CategoryTheory Limits AlgebraicTopology
open TernaryPoly TernaryPoly.FreeActionLinearization TernaryPoly.CoveringSingularOrbits
  TernaryPoly.SingularLocalCoefficient TernaryPoly.SingularLocalHomology
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.TopHomology

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep.{0} ℚ G)

/-- A chosen point of each fiber of a quotient covering. -/
def chosenFiber (b : B) : Fiber p b :=
  ⟨(hp.toIsQuotientMap.surjective b).choose, (hp.toIsQuotientMap.surjective b).choose_spec⟩

/-- A representation acts trivially. -/
def TrivialAction : Prop := ∀ (g : G) (v : V), V.ρ g v = v

variable {V}

theorem coeff_const (hV : TrivialAction V) (b : B) (c : FiberCoefficient p hp V b)
    (e e' : Fiber p b) : c.val e = c.val e' := by
  have hmem : e'.val ∈ MulAction.orbit G e.val :=
    (hp.apply_eq_iff_mem_orbit).mp (e'.property.trans e.property.symm)
  obtain ⟨g, hg⟩ := hmem
  have h1 : fiberSmul p hp g e = e' := Subtype.ext hg
  have h2 := c.property g e
  rw [h1] at h2
  rw [h2]
  exact (hV g _).symm


variable (V) in
/-- Fiber evaluation at the chosen point. -/
def fiberEquivT (b : B) : FiberCoefficient p hp V b ≃ₗ[ℚ] V :=
  coefficientEvaluationLinearEquiv p hp (chosenFiber p hp b)

theorem fiberEquivT_apply (b : B) (c : FiberCoefficient p hp V b) :
    fiberEquivT p hp V b c = c.val (chosenFiber p hp b) := rfl

theorem fiberEquivT_transport (hV : TrivialAction V) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (c : FiberCoefficient p hp V x) :
    fiberEquivT p hp V y (coefficientTransportLinear p hp γ c) = fiberEquivT p hp V x c := by
  have h := coefficientTransport_apply_transport p hp γ c (chosenFiber p hp x)
  rw [fiberEquivT_apply, fiberEquivT_apply]
  change (coefficientTransport p hp γ c).val (chosenFiber p hp y) = _
  rw [coeff_const p hp hV y (coefficientTransport p hp γ c) (chosenFiber p hp y)
    (fiberTransport p hp γ (chosenFiber p hp x))]
  exact h


section Chains

variable [ContinuousConstSMul G E] [IsCancelSMul G E]

open TernaryPoly.SingularLocalConstant (ordinaryChains ordinaryFinsuppIso ordinary_boundary_generator)

/-- Fiber evaluation identifies the local chains with finitely supported `V`-valued simplex chains. -/
def chainValueEquivT (n : ℕ) :
    VertexChain p hp V n ≃ₗ[ℚ] (SingularSimplex B n →₀ V) :=
  DFinsupp.mapRange.linearEquiv (fun σ => fiberEquivT p hp V (atVertex σ)) ≪≫ₗ
    (finsuppLequivDFinsupp ℚ).symm

omit [ContinuousConstSMul G E] [IsCancelSMul G E] in
theorem chainValueEquivT_single (n : ℕ) (σ : SingularSimplex B n)
    (c : FiberCoefficient p hp V (atVertex σ)) :
    chainValueEquivT p hp n (DFinsupp.single (β := fun τ : SingularSimplex B n =>
      FiberCoefficient p hp V (atVertex τ)) σ c) =
      Finsupp.single σ (fiberEquivT p hp V (atVertex σ) c) := by
  classical
  change (DFinsupp.mapRange (fun τ => fiberEquivT p hp V (atVertex τ)) (fun τ => map_zero _)
    (DFinsupp.single (β := fun τ : SingularSimplex B n =>
      FiberCoefficient p hp V (atVertex τ)) σ c)).toFinsupp = _
  rw [DFinsupp.mapRange_single, DFinsupp.toFinsupp_single]

/-- The comparison from local chains to ordinary `V`-coefficient chains. -/
def chainDegreeEquivT (n : ℕ) :
    VertexChain p hp V n ≃ₗ[ℚ] (ordinaryChains B (ModuleCat.of ℚ V)).X n :=
  chainValueEquivT p hp n ≪≫ₗ (ordinaryFinsuppIso B (ModuleCat.of ℚ V) n).symm.toLinearEquiv

omit [ContinuousConstSMul G E] [IsCancelSMul G E] in
theorem chainDegreeEquivT_single (n : ℕ) (σ : SingularSimplex B n)
    (c : FiberCoefficient p hp V (atVertex σ)) :
    chainDegreeEquivT p hp n (DFinsupp.single (β := fun τ : SingularSimplex B n =>
      FiberCoefficient p hp V (atVertex τ)) σ c) =
      ((TopCat.toSSet.obj B).ιChainComplex (R := ModuleCat.of ℚ V) σ)
        (fiberEquivT p hp V (atVertex σ) c) := by
  exact (congrArg (ordinaryFinsuppIso B (ModuleCat.of ℚ V) n).inv
    (chainValueEquivT_single p hp n σ c)).trans
    (TernaryPoly.SingularLocalConstant.ordinaryFinsuppIso_inv_single B (ModuleCat.of ℚ V) n σ _)

omit [ContinuousConstSMul G E] [IsCancelSMul G E] in
theorem chainDegreeEquivT_boundary_single (hV : TrivialAction V) (n : ℕ) (σ : SingularSimplex B (n+1))
    (c : FiberCoefficient p hp V (atVertex σ)) :
    chainDegreeEquivT p hp n (boundary p hp V n
      (DFinsupp.single (β := fun τ : SingularSimplex B (n+1) =>
        FiberCoefficient p hp V (atVertex τ)) σ c)) =
      (ordinaryChains B (ModuleCat.of ℚ V)).d (n+1) n (chainDegreeEquivT p hp (n+1)
        (DFinsupp.single (β := fun τ : SingularSimplex B (n+1) =>
          FiberCoefficient p hp V (atVertex τ)) σ c)) := by
  have hb := congrArg (chainDegreeEquivT p hp n) (boundary_single p hp V n σ c)
  refine hb.trans ?_
  rw [chainDegreeEquivT_single, ordinary_boundary_generator]
  refine (map_sum (chainDegreeEquivT p hp n) _ _).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  refine (map_zsmul (chainDegreeEquivT p hp n) _ _).trans ?_
  exact congrArg (fun v => (-1 : ℤ)^i.val • v)
    ((chainDegreeEquivT_single p hp n _ _).trans
      (congrArg ((TopCat.toSSet.obj B).ιChainComplex (R := ModuleCat.of ℚ V)
        (pullSimplex (simplexCoface n i) σ)) (fiberEquivT_transport p hp hV _ c)))

omit [ContinuousConstSMul G E] [IsCancelSMul G E] in
theorem chainDegreeEquivT_boundary (hV : TrivialAction V) (n : ℕ) :
    (chainDegreeEquivT (V := V) p hp n).toLinearMap.comp
        (boundary p hp V n : VertexChain p hp V (n+1) →ₗ[ℚ] VertexChain p hp V n) =
      ((ordinaryChains B (ModuleCat.of ℚ V)).d (n+1) n).hom.comp
        (chainDegreeEquivT (V := V) p hp (n+1)).toLinearMap :=
  DFinsupp.lhom_ext (M := fun σ : SingularSimplex B (n+1) =>
    FiberCoefficient p hp V (atVertex σ))
      (chainDegreeEquivT_boundary_single p hp hV n)

/-- **Trivial local systems on a free quotient covering are ordinary chains.** For a representation
with trivial action, the local-coefficient singular chains of the covering are isomorphic, by
fiber evaluation, to Mathlib's singular chains of the base with the same coefficient module. -/
def trivialLocalChainIso (hV : TrivialAction V) :
    localChains p hp V ≅ ordinaryChains B (ModuleCat.of ℚ V) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (chainDegreeEquivT p hp n).toModuleIso)
    (fun i j hij => by
      obtain rfl : i = j+1 := hij.symm
      apply ModuleCat.hom_ext
      simp only [localChains, ChainComplex.of_d]
      exact (chainDegreeEquivT_boundary p hp hV j).symm)

/-- On a path-connected base, `H₀` of the trivial local system is the coefficient module. -/
def trivialLocalH0Iso (hV : TrivialAction V) [PathConnectedSpace B] :
    (localChains p hp V).homology 0 ≅ ModuleCat.of ℚ V :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) 0).mapIso
    (trivialLocalChainIso p hp hV) ≪≫
    @asIso (ModuleCat.{0} ℚ) _ _ _ (B.singularHomology₀ε (ModuleCat.of ℚ V))
      (TopCat.instIsIsoSingularHomology₀εOfPathConnectedSpaceCarrier B (ModuleCat.of ℚ V))

end Chains

end TernaryPeriodPolynomials.Argument.TopHomology
