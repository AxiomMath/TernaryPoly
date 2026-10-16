module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Leibniz
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Degrees
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Generators

@[expose] public section


/-!
# Locality for Poincaré duality, E-level formulas: the lifted cap and the translate-sum pairing

For a quotient covering `p : E ⟶ B` with deck group `G` and a `G`-representation `V`:

* `chainDesc` : a linear map out of the scalar singular chains given on simplices;
* `liftChain p hp n` : the linear lift `C_n(B) → C_n(E)` through the chosen simplex lifts;
* `capE x a b` : the cap of an equivariant function `x : Simplex E a → V` with a chain of `E`, in the
  coinvariant model (`(back τ) ⊗ x(front τ)`), and `degreeEquiv_symm_cap`: the cap of the geometric
  local-coefficient cochain `φ` with a chain `c` of `B` is `capE (vertexToFunction φ)` of the lift of `c`;
* `Ysimp`, `Ybil`, `Yco` : given a scalar cochain `y` of `E` such that every simplex has only finitely many
  translates on which `y` does not vanish (`hfin`), the pairing `Yco : (V ⊗ C_b(E))_G → V`,
  `w ⊗ τ ↦ ∑_g y(g τ) ρ(g) w` (the translate sum), with `Yco_generator`, `Ysimp_smul` (well defined on
  coinvariants) and `Yco_d` : `Yco ∘ d = 0` when `y` is a cocycle.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TernaryPoly TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits TernaryPoly.SingularLocalCoefficient
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap TernaryPoly.EquivariantSingularResolution
open SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision

/-- A linear map out of the scalar singular chains, given on simplices. -/
def chainDesc {X : TopCat.{0}} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℚ M]
    (f : SingularSimplex X n → M) : singularChainGroup ℚ X n →ₗ[ℚ] M :=
  (Sigma.desc fun σ : SingularSimplex X n =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ M (f σ))).hom

theorem chainDesc_generator {X : TopCat.{0}} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℚ M]
    (f : SingularSimplex X n → M) (σ : SingularSimplex X n) :
    chainDesc f (chainGenerator ℚ X n σ) = f σ := by
  have h := congrArg (fun g : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ M => g.hom (1 : ℚ))
    (Sigma.ι_comp_desc (fun σ : SingularSimplex X n =>
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ M (f σ))) σ)
  exact h.trans (one_smul ℚ _)

theorem chainDesc_ext {X : TopCat.{0}} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℚ M]
    {f g : singularChainGroup ℚ X n →ₗ[ℚ] M}
    (h : ∀ σ, f (chainGenerator ℚ X n σ) = g (chainGenerator ℚ X n σ)) : f = g :=
  scalarChain_ext h

section Cap

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) (V : Rep.{0} ℚ G)

/-- The linear lift of scalar chains of the base through the chosen simplex lifts. -/
def liftChain [IsCancelSMul G E] (hp : IsQuotientCoveringMap p G) (n : ℕ) :
    singularChainGroup ℚ B n →ₗ[ℚ] singularChainGroup ℚ E n :=
  chainDesc fun σ => chainGenerator ℚ E n (chosenLift p hp n σ).val

/-- The cap in the coinvariant model, for a function `x` on simplices of `E`. -/
def capE (a b : ℕ) (x : SingularSimplex E a → V) :
    singularChainGroup ℚ E (a+b) →ₗ[ℚ] (coinvariantChains G E V).X b :=
  chainDesc fun τ => generator G E V b (backSimplex E a b τ) (x (frontSimplex E a b τ))

theorem capE_generator (a b : ℕ) (x : SingularSimplex E a → V) (τ : SingularSimplex E (a+b)) :
    capE V a b x (chainGenerator ℚ E (a+b) τ) =
      generator G E V b (backSimplex E a b τ) (x (frontSimplex E a b τ)) :=
  chainDesc_generator _ _

/-- The geometric cap, read in the coinvariant model through the lift of the chain. -/
theorem degreeEquiv_symm_cap [IsCancelSMul G E] (hp : IsQuotientCoveringMap p G) (a b : ℕ)
    (φ : VertexCochain p hp V a) (c : singularChainGroup ℚ B (a+b)) :
    (degreeEquiv p hp V b).symm (cap p hp V a b φ c) =
      capE V a b (vertexToFunction p hp φ) (liftChain p hp (a+b) c) := by
  have h : ((degreeEquiv p hp V b).symm.toLinearMap).comp (cap p hp V a b φ) =
      (capE V a b (vertexToFunction p hp φ)).comp (liftChain p hp (a+b)) := by
    apply chainDesc_ext
    intro σ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, liftChain, chainDesc_generator,
      capE_generator, cap_generator]
    exact capSimplex_lift p hp V a b φ (chosenLift p hp (a+b) σ)
  exact LinearMap.congr_fun h c

end Cap

section Pairing

variable {G : Type} [Group G] {E : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]

theorem smul_faceSimplex (n : ℕ) (g : G) (i : Fin (n+2)) (σ : SingularSimplex E (n+1)) :
    g • faceSimplex E n i σ = faceSimplex E n i (g • σ) := by
  rw [singular_smul_eq_map, singular_smul_eq_map]
  exact (ConcreteCategory.congr_hom
    ((TopCat.toSSet.map (scalarMap G E g)).naturality (SimplexCategory.δ i).op) σ)

variable (V : Rep.{0} ℚ G) {b : ℕ} (y : singularChainGroup ℚ E b →ₗ[ℚ] ℚ)
  (hfin : ∀ τ : SingularSimplex E b, {g : G | y (chainGenerator ℚ E b (g • τ)) ≠ 0}.Finite)

/-- The sum over the translates of a simplex of the `y`-weighted coefficient actions. -/
def Ysimp (τ : SingularSimplex E b) : V →ₗ[ℚ] V :=
  ∑ g ∈ (hfin τ).toFinset, y (chainGenerator ℚ E b (g • τ)) • V.ρ g

include hfin in
theorem Ysimp_apply (τ : SingularSimplex E b) (w : V) :
    Ysimp V y hfin τ w = ∑ g ∈ (hfin τ).toFinset, y (chainGenerator ℚ E b (g • τ)) • V.ρ g w := by
  simp [Ysimp, LinearMap.sum_apply]

include hfin in
theorem Ysimp_apply_of_superset (τ : SingularSimplex E b) (S : Finset G)
    (hS : ∀ g, y (chainGenerator ℚ E b (g • τ)) ≠ 0 → g ∈ S) (w : V) :
    Ysimp V y hfin τ w = ∑ g ∈ S, y (chainGenerator ℚ E b (g • τ)) • V.ρ g w := by
  rw [Ysimp_apply]
  apply Finset.sum_subset
  · intro g hg
    rw [Set.Finite.mem_toFinset] at hg
    exact hS g hg
  · intro g _ hg
    rw [Set.Finite.mem_toFinset] at hg
    have : y (chainGenerator ℚ E b (g • τ)) = 0 := by
      by_contra h; exact hg h
    rw [this, zero_smul]

/-- The bilinear form `(w, c) ↦ ∑_g y(g c) ρ(g) w`. -/
def Ybil : V →ₗ[ℚ] singularChainGroup ℚ E b →ₗ[ℚ] V :=
  (chainDesc (M := V →ₗ[ℚ] V) fun τ => Ysimp V y hfin τ).flip

theorem Ybil_generator (w : V) (τ : SingularSimplex E b) :
    Ybil V y hfin w (chainGenerator ℚ E b τ) = Ysimp V y hfin τ w := by
  simp [Ybil, chainDesc_generator]

theorem Ysimp_smul (g0 : G) (τ : SingularSimplex E b) (w : V) :
    Ysimp V y hfin (g0 • τ) (V.ρ g0 w) = Ysimp V y hfin τ w := by
  rw [Ysimp_apply, Ysimp_apply]
  refine Finset.sum_nbij' (fun g => g * g0) (fun g => g * g0⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    rw [Set.Finite.mem_toFinset] at hg ⊢
    change y (chainGenerator ℚ E b ((g * g0) • τ)) ≠ 0
    rw [mul_smul]; exact hg
  · intro g hg
    rw [Set.Finite.mem_toFinset] at hg ⊢
    change y (chainGenerator ℚ E b ((g * g0⁻¹) • (g0 • τ))) ≠ 0
    rw [← mul_smul, inv_mul_cancel_right]; exact hg
  · intro g _; simp
  · intro g _; simp
  · intro g _
    rw [mul_smul, map_mul]
    rfl

/-- The `y`-pairing on the tensor product. -/
def YTensor : TensorProduct ℚ V (chainRep G E b) →ₗ[ℚ] V :=
  TensorProduct.lift (Ybil V y hfin)

theorem YTensor_invariant (g : G) :
    YTensor V y hfin ∘ₗ (V.ρ.tprod (chainRep G E b).ρ g) = YTensor V y hfin := by
  apply TensorProduct.ext'
  intro w c
  rw [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul, YTensor,
    TensorProduct.lift.tmul, TensorProduct.lift.tmul]
  have h : (Ybil V y hfin (V.ρ g w)).comp ((chainRep G E b).ρ g) = Ybil V y hfin w := by
    apply chainDesc_ext
    intro τ
    rw [LinearMap.comp_apply]
    have hc : (chainRep G E b).ρ g (chainGenerator ℚ E b τ) = chainGenerator ℚ E b (g • τ) :=
      chainElement_smul G E b g τ
    rw [hc, Ybil_generator, Ybil_generator, Ysimp_smul]
  exact LinearMap.congr_fun h c

/-- **The translate-sum pairing on coinvariant singular chains**:
`w ⊗ τ ↦ ∑_g y(g τ) ρ(g) w`. -/
def Yco : (coinvariantChains G E V).X b →ₗ[ℚ] V :=
  Representation.Coinvariants.lift _ (YTensor V y hfin) (YTensor_invariant V y hfin)

theorem Yco_generator (τ : SingularSimplex E b) (w : V) :
    Yco V y hfin (generator G E V b τ w) = Ysimp V y hfin τ w := by
  change YTensor V y hfin (w ⊗ₜ[ℚ] (chainElement G E b τ)) = _
  rw [YTensor, TensorProduct.lift.tmul]
  exact Ybil_generator V y hfin w τ

theorem Ysimp_boundary (hy : ∀ e, y ((singularBoundary ℚ E b).hom e) = 0)
    (τ : SingularSimplex E (b+1)) (w : V) :
    ∑ i : Fin (b+2), (-1 : ℤ)^i.val • Ysimp V y hfin (faceSimplex E b i τ) w = 0 := by
  let S : Finset G :=
    Finset.univ.biUnion fun i : Fin (b+2) => (hfin (faceSimplex E b i τ)).toFinset
  have hS : ∀ i : Fin (b+2), ∀ g,
      y (chainGenerator ℚ E b (g • faceSimplex E b i τ)) ≠ 0 → g ∈ S := by
    intro i g hg
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and, Set.Finite.mem_toFinset]
    exact ⟨i, hg⟩
  have h1 : ∀ i : Fin (b+2), Ysimp V y hfin (faceSimplex E b i τ) w =
      ∑ g ∈ S, y (chainGenerator ℚ E b (g • faceSimplex E b i τ)) • V.ρ g w :=
    fun i => Ysimp_apply_of_superset V y hfin _ S (hS i) w
  simp_rw [h1, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro g _
  have h2 : ∑ i : Fin (b+2), (-1 : ℤ)^i.val •
        (y (chainGenerator ℚ E b (g • faceSimplex E b i τ)) • V.ρ g w) =
      (∑ i : Fin (b+2), (-1 : ℤ)^i.val •
        y (chainGenerator ℚ E b (g • faceSimplex E b i τ))) • V.ρ g w := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_assoc]
  rw [h2]
  have h3 : ∑ i : Fin (b+2), (-1 : ℤ)^i.val •
      y (chainGenerator ℚ E b (g • faceSimplex E b i τ)) = 0 := by
    have := hy (chainGenerator ℚ E (b+1) (g • τ))
    rw [scalarBoundary_generator, map_sum] at this
    simp only [map_zsmul, smul_faceSimplex] at this ⊢
    exact this
  rw [h3, zero_smul]

/-- For a cocycle `y`, the translate-sum pairing vanishes on boundaries. -/
theorem Yco_d (hy : ∀ e, y ((singularBoundary ℚ E b).hom e) = 0)
    (e : (coinvariantChains G E V).X (b+1)) :
    Yco V y hfin ((coinvariantChains G E V).d (b+1) b e) = 0 := by
  have h : (Yco V y hfin).comp ((coinvariantChains G E V).d (b+1) b).hom = 0 := by
    apply Representation.Coinvariants.hom_ext
    apply TensorProduct.ext'
    intro w c
    let L : singularChainGroup ℚ E (b+1) →ₗ[ℚ] V :=
      (Yco V y hfin).comp (((coinvariantChains G E V).d (b+1) b).hom.comp
        ((Representation.Coinvariants.mk _).comp
          (TensorProduct.mk ℚ V (chainRep G E (b+1)) w)))
    have hL : L = 0 := by
      apply chainDesc_ext
      intro τ
      show Yco V y hfin (((coinvariantChains G E V).d (b+1) b)
          (generator G E V (b+1) τ w)) = 0
      rw [generator_boundary, map_sum]
      simp only [map_zsmul, Yco_generator]
      exact Ysimp_boundary V y hfin hy τ w
    exact LinearMap.congr_fun hL c
  exact LinearMap.congr_fun h e

/-- The pairing takes equal values on homologous cycles. -/
theorem Yco_eq_of_sub (hy : ∀ e, y ((singularBoundary ℚ E b).hom e) = 0)
    {ζ τ : (coinvariantChains G E V).X b} (v : (coinvariantChains G E V).X (b+1))
    (h : ζ - τ = (coinvariantChains G E V).d (b+1) b v) :
    Yco V y hfin ζ = Yco V y hfin τ := by
  have := Yco_d V y hfin hy v
  rw [← h, map_sub] at this
  exact sub_eq_zero.mp this

end Pairing

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
