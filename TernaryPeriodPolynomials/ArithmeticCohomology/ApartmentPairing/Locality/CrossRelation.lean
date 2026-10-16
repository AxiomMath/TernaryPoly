module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.NormalizationGeometry
public import TernaryPeriodPolynomials.Topology.SingularLocal.Constant.Tensor
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Leibniz
public import TernaryPeriodPolynomials.Topology.SingularHomology.SubordinateChains
public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.CapSupportComplex

@[expose] public section


/-!
# Locality for Poincaré duality: the cross relation (Euclidean core)

Constant-coefficient algebra on a space `X` with two closed sets `Wset` (where a relative cocycle is
supported) and `Zs` (where a Thom cochain `y` is supported).  For a `V`-valued cochain `φ` we form
`capPairF y φ : C_{a+b} → V`, `σ ↦ y(back σ) • φ(front σ)`; this is `y ∘ (φ ∩ -)` read in the tensor
model `C_b ⊗ V` of the constant local chains (`capPair_eq_capPairF`), and it has the signed Leibniz
rule `capPairF_leibniz` (derived from the library's `cap_leibniz`) and the two support lemmas
(`capPairF_eq_zero_of_front`, `capPairF_eq_zero_of_back`).

`cross_relation`: if the relative `H₂(X, X∖Wset)` is spanned by a class `[a]`, `cc` is a relative
5-chain of the triad `(X; X∖Wset, X∖Zs)` and `y` is a cocycle vanishing off `Zs`, then there is one
scalar `r`, independent of the coefficient module `V` and of the relative cocycle `φ`, with
`⟨y, φ ∩ cc⟩ = r • φ(a)`.  The universal-coefficient step is pure linear algebra over `ℚ`
(`exists_cobounding`: a functional vanishing on all relative cycles is a relative coboundary).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical TensorProduct Simplicial

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TernaryPoly TernaryPoly.SingularLocalConstant TernaryPoly.SingularLocalCap
  TernaryPoly.SingularLocalCapNormalization
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision

variable (X : TopCat.{0}) (V : ModuleCat.{0} ℚ)

/-- The cap of a constant-coefficient cochain with a scalar chain, read in the tensor model
`C_b ⊗ V` of the constant local chains. -/
def capT (a b : ℕ) (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a) :
    singularChainGroup ℚ X (a+b) →ₗ[ℚ] (scalarChains X).X b ⊗[ℚ] V :=
  ((localTensorChainIso X V).hom.f b).hom.comp (cap (𝟙 X) (identityCover X) (constantRep V) a b φ)

theorem localTensorChainIso_single (b : ℕ) (σ : SingularSimplex X b)
    (c : FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex σ)) :
    ((localTensorChainIso X V).hom.f b).hom (DFinsupp.single (β := fun τ : SingularSimplex X b =>
      FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex τ)) σ c) =
      chainGenerator ℚ X b σ ⊗ₜ[ℚ] (fiberEquiv X V (atVertex σ) c) := by
  apply (tensorDegreeEquiv X V b).injective
  have h1 : (tensorDegreeEquiv X V b) (((localTensorChainIso X V).hom.f b).hom
      (DFinsupp.single (β := fun τ : SingularSimplex X b =>
        FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex τ)) σ c)) =
      chainDegreeEquiv X V b (DFinsupp.single (β := fun τ : SingularSimplex X b =>
        FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex τ)) σ c) := by
    change (tensorDegreeEquiv X V b) ((tensorDegreeEquiv X V b).symm (chainDegreeEquiv X V b _)) = _
    exact LinearEquiv.apply_symm_apply _ _
  rw [h1, chainDegreeEquiv_single, tensorDegreeEquiv_generator]

theorem capT_generator (a b : ℕ) (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a)
    (σ : SingularSimplex X (a+b)) :
    capT X V a b φ (chainGenerator ℚ X (a+b) σ) =
      chainGenerator ℚ X b (backSimplex X a b σ) ⊗ₜ[ℚ]
        evaluation X V a φ (chainGenerator ℚ X a (frontSimplex X a b σ)) := by
  show ((localTensorChainIso X V).hom.f b).hom
    (cap (𝟙 X) (identityCover X) (constantRep V) a b φ (chainGenerator ℚ X (a+b) σ)) = _
  erw [cap_generator]
  have h : capSimplex (𝟙 X) (identityCover X) (constantRep V) a b σ φ =
      DFinsupp.single (β := fun τ : SingularSimplex X b =>
        FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) (atVertex τ)) (backSimplex X a b σ)
        (capCoefficient (𝟙 X) (identityCover X) (constantRep V) a b σ φ) := rfl
  erw [h, localTensorChainIso_single, evaluation_generator, capCoefficient_value]

theorem localTensorChainIso_boundary (b : ℕ)
    (ξ : VertexChain (𝟙 X) (identityCover X) (constantRep V) (b+1)) :
    ((localTensorChainIso X V).hom.f b).hom
        (boundary (𝟙 X) (identityCover X) (constantRep V) b ξ) =
      tensorDifferential X V b (((localTensorChainIso X V).hom.f (b+1)).hom ξ) := by
  have h := congrArg (fun f => f.hom ξ) ((localTensorChainIso X V).hom.comm (b+1) b)
  simp only [chains, localChains, tensorChains, ChainComplex.of_d] at h
  exact h.symm

/-- Pairing of the tensor chains `C_n ⊗ V` with a scalar functional on `C_n`. -/
def yPair (n : ℕ) (y : (scalarChains X).X n →ₗ[ℚ] ℚ) :
    (scalarChains X).X n ⊗[ℚ] V →ₗ[ℚ] V :=
  (TensorProduct.lid ℚ V).toLinearMap ∘ₗ TensorProduct.map y LinearMap.id

theorem yPair_tmul (n : ℕ) (y : (scalarChains X).X n →ₗ[ℚ] ℚ) (c : (scalarChains X).X n) (v : V) :
    yPair X V n y (c ⊗ₜ[ℚ] v) = y c • v := by
  simp [yPair]

/-! ### Support of simplicial operators -/

open SphereOddDegree in
theorem isSubordinate_map {S : Set X} {n m : ℕ} (g : (⦋n⦌ : SimplexCategory) ⟶ ⦋m⦌)
    (σ : singularSimplices X m) (hσ : IsSubordinate S σ) :
    IsSubordinate S ((TopCat.toSSet.obj X).map g.op σ) := by
  refine IsSubordinate.comp_of_range_subset (σ := σ) (SimplexCategory.toTop₀.map g).hom ?_ hσ
  exact toSSetObjEquiv_map_op_naturality X n m g σ

open SphereOddDegree in
theorem isSubordinate_front {S : Set X} (a b : ℕ) (σ : SingularSimplex X (a+b))
    (hσ : IsSubordinate S σ) : IsSubordinate S (frontSimplex X a b σ) :=
  isSubordinate_map X _ σ hσ

open SphereOddDegree in
theorem isSubordinate_back {S : Set X} (a b : ℕ) (σ : SingularSimplex X (a+b))
    (hσ : IsSubordinate S σ) : IsSubordinate S (backSimplex X a b σ) :=
  isSubordinate_map X _ σ hσ

/-! ### The pairing `y ∘ (φ ∩ -)` and its properties -/

/-- Cap a constant-coefficient cochain with a scalar chain, then pair the tensor chains with the
scalar functional `y`. -/
def capPair (a b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a) :
    singularChainGroup ℚ X (a+b) →ₗ[ℚ] V :=
  (yPair X V b y).comp (capT X V a b φ)

theorem capPair_generator (a b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a) (σ : SingularSimplex X (a+b)) :
    capPair X V a b y φ (chainGenerator ℚ X (a+b) σ) =
      y (chainGenerator ℚ X b (backSimplex X a b σ)) •
        evaluation X V a φ (chainGenerator ℚ X a (frontSimplex X a b σ)) := by
  simp only [capPair, LinearMap.comp_apply]
  rw [capT_generator, yPair_tmul]

open SphereOddDegree in
theorem capT_eq_zero_of_front {U : Set X} (a b : ℕ)
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a)
    (hφ : ∀ τ : SingularSimplex X a, IsSubordinate U τ → evaluation X V a φ (chainGenerator ℚ X a τ) = 0)
    {c : singularChainGroup ℚ X (a+b)} (hc : c ∈ subChainSubmodule ℚ X U (a+b)) :
    capT X V a b φ c = 0 := by
  refine subChainSubmodule_induction (S := U) (p := fun x => capT X V a b φ x = 0) ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    rw [capT_generator, hφ _ (isSubordinate_front X a b σ hσ), TensorProduct.tmul_zero]
  · exact map_zero _
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]
  · intro r x hx
    rw [map_smul, hx, smul_zero]

open SphereOddDegree in
theorem capPair_eq_zero_of_back {U : Set X} (a b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a)
    (hy : ∀ τ : SingularSimplex X b, IsSubordinate U τ → y (chainGenerator ℚ X b τ) = 0)
    {c : singularChainGroup ℚ X (a+b)} (hc : c ∈ subChainSubmodule ℚ X U (a+b)) :
    capPair X V a b y φ c = 0 := by
  refine subChainSubmodule_induction (S := U) (p := fun x => capPair X V a b y φ x = 0) ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    rw [capPair_generator, hy _ (isSubordinate_back X a b σ hσ), zero_smul]
  · exact map_zero _
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]
  · intro r x hx
    rw [map_smul, hx, smul_zero]

open SphereOddDegree in
theorem capPair_eq_zero_of_front {U : Set X} (a b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a)
    (hφ : ∀ τ : SingularSimplex X a, IsSubordinate U τ → evaluation X V a φ (chainGenerator ℚ X a τ) = 0)
    {c : singularChainGroup ℚ X (a+b)} (hc : c ∈ subChainSubmodule ℚ X U (a+b)) :
    capPair X V a b y φ c = 0 := by
  simp only [capPair, LinearMap.comp_apply]
  rw [capT_eq_zero_of_front X V a b φ hφ hc, map_zero]

theorem yPair_tensorDifferential (b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (hy : ∀ e, y ((singularBoundary ℚ X b).hom e) = 0)
    (e : (scalarChains X).X (b+1) ⊗[ℚ] V) :
    yPair X V b y (tensorDifferential X V b e) = 0 := by
  induction e using TensorProduct.inductionOn with
  | tmul c v =>
    change yPair X V b y (((singularBoundary ℚ X b).hom c) ⊗ₜ[ℚ] v) = 0
    rw [yPair_tmul, hy, zero_smul]
  | add u w hu hw => rw [map_add, map_add, hu, hw, add_zero]

/-- Leibniz rule for the pairing with a cocycle `y`: the coboundary of `φ` capped with `c` pairs as
`φ` capped with the boundary of `c`. -/
theorem capPair_leibniz (a b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (hy : ∀ e, y ((singularBoundary ℚ X b).hom e) = 0)
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a)
    (c : singularChainGroup ℚ X (a+b+1)) :
    capPair X V (a+1) b y (differential (𝟙 X) (identityCover X) (constantRep V) a φ)
        (scalarCastLeft X a b c) =
      capPair X V a b y φ ((singularBoundary ℚ X (a+b)).hom c) := by
  have h := cap_leibniz (𝟙 X) (identityCover X) (constantRep V) a b φ c
  let L : VertexChain (𝟙 X) (identityCover X) (constantRep V) b →ₗ[ℚ] V :=
    (yPair X V b y).comp ((localTensorChainIso X V).hom.f b).hom
  have h2 := (congrArg L h).trans ((L.map_add _ _).trans
    (congrArg (fun t => L (cap (𝟙 X) (identityCover X) (constantRep V) (a+1) b
      (differential (𝟙 X) (identityCover X) (constantRep V) a φ) (scalarCastLeft X a b c)) + t)
      (map_zsmul L ((-1 : ℤ)^a) _)))
  have h3 : L (boundary (𝟙 X) (identityCover X) (constantRep V) b
      (cap (𝟙 X) (identityCover X) (constantRep V) a (b+1) φ c)) = 0 := by
    change yPair X V b y (((localTensorChainIso X V).hom.f b).hom _) = 0
    rw [localTensorChainIso_boundary]
    exact yPair_tensorDifferential X V b y hy _
  rw [h3, smul_zero, add_zero] at h2
  exact h2.symm

/-! ### Plain-hom form of the pairing -/

/-- The pairing `y ∘ (f ∩ -)` for a plain `V`-valued cochain `f : C_a → V`:
on a simplex `σ` it is `y(back σ) • f(front σ)`. -/
def capPairF (a b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (f : singularChainGroup ℚ X a →ₗ[ℚ] V) : singularChainGroup ℚ X (a+b) →ₗ[ℚ] V :=
  (Sigma.desc fun σ : SingularSimplex X (a+b) => ModuleCat.ofHom
    (LinearMap.toSpanSingleton ℚ V
      (y (chainGenerator ℚ X b (backSimplex X a b σ)) •
        f (chainGenerator ℚ X a (frontSimplex X a b σ))))).hom

theorem capPairF_generator (a b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (f : singularChainGroup ℚ X a →ₗ[ℚ] V) (σ : SingularSimplex X (a+b)) :
    capPairF X V a b y f (chainGenerator ℚ X (a+b) σ) =
      y (chainGenerator ℚ X b (backSimplex X a b σ)) •
        f (chainGenerator ℚ X a (frontSimplex X a b σ)) := by
  have h := congrArg (fun g : ModuleCat.of ℚ ℚ ⟶ V => g.hom (1 : ℚ))
    (Sigma.ι_comp_desc (fun σ : SingularSimplex X (a+b) => ModuleCat.ofHom
      (LinearMap.toSpanSingleton ℚ V
        (y (chainGenerator ℚ X b (backSimplex X a b σ)) •
          f (chainGenerator ℚ X a (frontSimplex X a b σ))))) σ)
  exact h.trans (one_smul ℚ _)

theorem capPair_eq_capPairF (a b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a) :
    capPair X V a b y φ = capPairF X V a b y (evaluation X V a φ) := by
  apply scalarChain_ext
  intro σ
  rw [capPair_generator, capPairF_generator]

theorem capPairF_add (a b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (f g : singularChainGroup ℚ X a →ₗ[ℚ] V) :
    capPairF X V a b y (f + g) = capPairF X V a b y f + capPairF X V a b y g := by
  apply scalarChain_ext
  intro σ
  simp only [LinearMap.add_apply, capPairF_generator, smul_add]

theorem capPairF_sub (a b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (f g : singularChainGroup ℚ X a →ₗ[ℚ] V) :
    capPairF X V a b y (f - g) = capPairF X V a b y f - capPairF X V a b y g := by
  apply scalarChain_ext
  intro σ
  simp only [LinearMap.sub_apply, capPairF_generator, smul_sub]

/-- Tensoring a scalar cochain with a vector `v`. -/
theorem capPairF_smulRight (a b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (f : singularChainGroup ℚ X a →ₗ[ℚ] ℚ) (v : V) (c : singularChainGroup ℚ X (a+b)) :
    capPairF X V a b y (f.smulRight v) c =
      capPairF X (ModuleCat.of ℚ ℚ) a b y f c • v := by
  have : capPairF X V a b y (f.smulRight v) =
      (LinearMap.toSpanSingleton ℚ V v).comp (capPairF X (ModuleCat.of ℚ ℚ) a b y f) := by
    apply scalarChain_ext
    intro σ
    rw [LinearMap.comp_apply, capPairF_generator, capPairF_generator, LinearMap.smulRight_apply,
      LinearMap.toSpanSingleton_apply]
    exact (smul_assoc _ _ v).symm
  rw [this]
  rfl

theorem capPairF_eq_zero_of_front {U : Set X} (a b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (f : singularChainGroup ℚ X a →ₗ[ℚ] V)
    (hf : ∀ τ : SingularSimplex X a, SphereOddDegree.IsSubordinate U τ →
      f (chainGenerator ℚ X a τ) = 0)
    {c : singularChainGroup ℚ X (a+b)} (hc : c ∈ SphereOddDegree.subChainSubmodule ℚ X U (a+b)) :
    capPairF X V a b y f c = 0 := by
  refine SphereOddDegree.subChainSubmodule_induction (S := U)
    (p := fun x => capPairF X V a b y f x = 0) ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    rw [capPairF_generator, hf _ (isSubordinate_front X a b σ hσ), smul_zero]
  · exact map_zero _
  · intro x z hx hz
    rw [map_add, hx, hz, add_zero]
  · intro r x hx
    rw [map_smul, hx, smul_zero]

theorem capPairF_eq_zero_of_back {U : Set X} (a b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (f : singularChainGroup ℚ X a →ₗ[ℚ] V)
    (hy : ∀ τ : SingularSimplex X b, SphereOddDegree.IsSubordinate U τ →
      y (chainGenerator ℚ X b τ) = 0)
    {c : singularChainGroup ℚ X (a+b)} (hc : c ∈ SphereOddDegree.subChainSubmodule ℚ X U (a+b)) :
    capPairF X V a b y f c = 0 := by
  refine SphereOddDegree.subChainSubmodule_induction (S := U)
    (p := fun x => capPairF X V a b y f x = 0) ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    rw [capPairF_generator, hy _ (isSubordinate_back X a b σ hσ), zero_smul]
  · exact map_zero _
  · intro x z hx hz
    rw [map_add, hx, hz, add_zero]
  · intro r x hx
    rw [map_smul, hx, smul_zero]

theorem evaluation_differential (a : ℕ)
    (φ : VertexCochain (𝟙 X) (identityCover X) (constantRep V) a)
    (c : singularChainGroup ℚ X (a+1)) :
    evaluation X V (a+1) (differential (𝟙 X) (identityCover X) (constantRep V) a φ) c =
      evaluation X V a φ ((singularBoundary ℚ X a).hom c) := by
  have h := TernaryPoly.EuclideanCompactCap.ordinaryEvaluation_d X V a (a+1) φ c
  simp only [cochains, localCochains, CochainComplex.of_d] at h
  exact h

/-- Plain-hom Leibniz rule. -/
theorem capPairF_leibniz (a b : ℕ) (y : (scalarChains X).X b →ₗ[ℚ] ℚ)
    (hy : ∀ e, y ((singularBoundary ℚ X b).hom e) = 0)
    (ψ : singularChainGroup ℚ X a →ₗ[ℚ] V) (c : singularChainGroup ℚ X (a+b+1)) :
    capPairF X V (a+1) b y (ψ.comp (singularBoundary ℚ X a).hom) (scalarCastLeft X a b c) =
      capPairF X V a b y ψ ((singularBoundary ℚ X (a+b)).hom c) := by
  have h := capPair_leibniz X V a b y hy ((cochainHomEquiv X V a).symm ψ) c
  have e1 : evaluation X V a ((cochainHomEquiv X V a).symm ψ) = ψ :=
    (cochainHomEquiv X V a).apply_symm_apply ψ
  have e2 : evaluation X V (a+1) (differential (𝟙 X) (identityCover X) (constantRep V) a
      ((cochainHomEquiv X V a).symm ψ)) = ψ.comp (singularBoundary ℚ X a).hom := by
    apply LinearMap.ext
    intro z
    rw [evaluation_differential, e1]
    rfl
  have h1 := LinearMap.congr_fun (capPair_eq_capPairF X V (a+1) b y
    (differential (𝟙 X) (identityCover X) (constantRep V) a ((cochainHomEquiv X V a).symm ψ)))
    (scalarCastLeft X a b c)
  have h2 := LinearMap.congr_fun (capPair_eq_capPairF X V a b y ((cochainHomEquiv X V a).symm ψ))
    ((singularBoundary ℚ X (a+b)).hom c)
  rw [e2] at h1
  rw [e1] at h2
  exact h1.symm.trans (h.trans h2)

open SphereOddDegree in
theorem awCastSimplex_one_three (σ : SingularSimplex X (1+3+1)) :
    awCastSimplex X 1 3 σ = σ := by
  have h : awCastLeft 1 3 = 𝟙 _ := rfl
  unfold awCastSimplex
  rw [h]
  simp

theorem scalarCastLeft_one_three (c : singularChainGroup ℚ X (1+3+1)) :
    (scalarCastLeft X 1 3 c : singularChainGroup ℚ X 5) = c := by
  have : (scalarCastLeft X 1 3 : singularChainGroup ℚ X (1+3+1) →ₗ[ℚ] singularChainGroup ℚ X 5) =
      LinearMap.id := by
    apply scalarChain_ext
    intro σ
    rw [scalarCastLeft_generator, awCastSimplex_one_three]
    rfl
  exact LinearMap.congr_fun this c

/-! ### Linear algebra over `ℚ` -/

theorem exists_comp_eq_of_ker_le {M N P : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N] [AddCommGroup P] [Module ℚ P]
    (G : M →ₗ[ℚ] N) (Φ : M →ₗ[ℚ] P) (h : LinearMap.ker G ≤ LinearMap.ker Φ) :
    ∃ ψ : N →ₗ[ℚ] P, ψ.comp G = Φ := by
  let ψ₀ : LinearMap.range G →ₗ[ℚ] P :=
    ((LinearMap.ker G).liftQ Φ h).comp (G.quotKerEquivRange.symm : LinearMap.range G →ₗ[ℚ] _)
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend ψ₀
  refine ⟨ψ, ?_⟩
  apply LinearMap.ext
  intro m
  have h1 := LinearMap.congr_fun hψ ⟨G m, ⟨m, rfl⟩⟩
  have h2 : (G.quotKerEquivRange.symm ⟨G m, ⟨m, rfl⟩⟩) = Submodule.Quotient.mk m :=
    LinearMap.quotKerEquivRange_symm_apply_image G m ⟨m, rfl⟩ |>.trans rfl
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
  change ψ (G m) = Φ m
  rw [h1]
  change ((LinearMap.ker G).liftQ Φ h) (G.quotKerEquivRange.symm ⟨G m, ⟨m, rfl⟩⟩) = Φ m
  rw [h2]
  rfl

/-- A functional vanishing on all relative cycles is a relative coboundary. -/
theorem exists_cobounding {C₂ C₁ V : Type*} [AddCommGroup C₂] [Module ℚ C₂]
    [AddCommGroup C₁] [Module ℚ C₁] [AddCommGroup V] [Module ℚ V]
    (d : C₂ →ₗ[ℚ] C₁) (S₁ : Submodule ℚ C₁) (f : C₂ →ₗ[ℚ] V)
    (hf : ∀ z, d z ∈ S₁ → f z = 0) :
    ∃ ψ : C₁ →ₗ[ℚ] V, (∀ s ∈ S₁, ψ s = 0) ∧ ψ.comp d = f := by
  let G : (C₂ × S₁) →ₗ[ℚ] C₁ := d.coprod S₁.subtype
  let Φ : (C₂ × S₁) →ₗ[ℚ] V := f.coprod 0
  have hk : LinearMap.ker G ≤ LinearMap.ker Φ := by
    rintro ⟨z, s⟩ hzs
    have hz : d z + (s : C₁) = 0 := by simpa [G] using hzs
    have : d z ∈ S₁ := by
      have : d z = -(s : C₁) := eq_neg_of_add_eq_zero_left hz
      rw [this]; exact S₁.neg_mem s.2
    simp [Φ, hf z this]
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_ker_le G Φ hk
  refine ⟨ψ, ?_, ?_⟩
  · intro s hs
    have := LinearMap.congr_fun hψ (0, ⟨s, hs⟩)
    simpa [G, Φ] using this
  · apply LinearMap.ext
    intro z
    have := LinearMap.congr_fun hψ (z, 0)
    simpa [G, Φ] using this

/-! ### The cross relation -/

open SphereOddDegree in
theorem vanish_on_sub {V : Type*} [AddCommGroup V] [Module ℚ V] {U : Set X} {n : ℕ}
    (f : singularChainGroup ℚ X n →ₗ[ℚ] V)
    (hf : ∀ τ : SingularSimplex X n, IsSubordinate U τ → f (chainGenerator ℚ X n τ) = 0)
    {z : singularChainGroup ℚ X n} (hz : z ∈ subChainSubmodule ℚ X U n) : f z = 0 := by
  refine subChainSubmodule_induction (S := U) (p := fun x => f x = 0) ?_ ?_ ?_ ?_ hz
  · exact hf
  · exact map_zero _
  · intro x w hx hw
    rw [map_add, hx, hw, add_zero]
  · intro r x hx
    rw [map_smul, hx, smul_zero]

open SphereOddDegree in
/-- The core of the cross relation: a relative cocycle that agrees with `φ₀ ⊗ v` on the generator
`a` of the relative `H₂` has the same pairing with `cc` as `φ₀ ⊗ v`. -/
theorem cross_core (Wset Zs : Set X) (y : (scalarChains X).X 3 →ₗ[ℚ] ℚ)
    (hy : ∀ e, y ((singularBoundary ℚ X 3).hom e) = 0)
    (hyv : ∀ τ : SingularSimplex X 3, IsSubordinate Zsᶜ τ → y (chainGenerator ℚ X 3 τ) = 0)
    (a : singularChainGroup ℚ X 2)
    (cc : singularChainGroup ℚ X 5)
    (hcc : (singularBoundary ℚ X 4).hom cc ∈
      subChainSubmodule ℚ X Wsetᶜ 4 ⊔ subChainSubmodule ℚ X Zsᶜ 4)
    (hspan : ∀ z : singularChainGroup ℚ X 2, (singularBoundary ℚ X 1).hom z ∈
      subChainSubmodule ℚ X Wsetᶜ 1 → ∃ (q : ℚ) (f : singularChainGroup ℚ X 3),
        z - q • a - (singularBoundary ℚ X 2).hom f ∈ subChainSubmodule ℚ X Wsetᶜ 2)
    (V : ModuleCat.{0} ℚ) (φ : singularChainGroup ℚ X 2 →ₗ[ℚ] V)
    (φ₀ : singularChainGroup ℚ X 2 →ₗ[ℚ] ℚ) (v : V)
    (hφS : ∀ τ : SingularSimplex X 2, IsSubordinate Wsetᶜ τ → φ (chainGenerator ℚ X 2 τ) = 0)
    (hφd : ∀ e, φ ((singularBoundary ℚ X 2).hom e) = 0)
    (hφ₀S : ∀ τ : SingularSimplex X 2, IsSubordinate Wsetᶜ τ → φ₀ (chainGenerator ℚ X 2 τ) = 0)
    (hφ₀d : ∀ e, φ₀ ((singularBoundary ℚ X 2).hom e) = 0)
    (hav : φ a = φ₀ a • v) :
    capPairF X V 2 3 y φ cc = capPairF X (ModuleCat.of ℚ ℚ) 2 3 y φ₀ cc • v := by
  set φ' : singularChainGroup ℚ X 2 →ₗ[ℚ] V := φ - φ₀.smulRight v with hφ'
  have hφ'S : ∀ z ∈ subChainSubmodule ℚ X Wsetᶜ 2, φ' z = 0 := by
    intro z hz
    have h1 := vanish_on_sub X φ hφS hz
    have h2 := vanish_on_sub X φ₀ hφ₀S hz
    simp [hφ', h1, h2]
  have hφ'd : ∀ e, φ' ((singularBoundary ℚ X 2).hom e) = 0 := by
    intro e
    simp [hφ', hφd, hφ₀d]
  have hφ'a : φ' a = 0 := by
    simp [hφ', hav]
  have hcyc : ∀ z, (singularBoundary ℚ X 1).hom z ∈ subChainSubmodule ℚ X Wsetᶜ 1 → φ' z = 0 := by
    intro z hz
    obtain ⟨q, f, hqf⟩ := hspan z hz
    have h1 := hφ'S _ hqf
    have h2 : φ' z = φ' (z - q • a - (singularBoundary ℚ X 2).hom f) + q • φ' a +
        φ' ((singularBoundary ℚ X 2).hom f) := by
      rw [map_sub, map_sub, map_smul]; abel
    rw [h2, h1, hφ'a, hφ'd]
    simp
  obtain ⟨ψ, hψS, hψ⟩ := exists_cobounding (singularBoundary ℚ X 1).hom
    (subChainSubmodule ℚ X Wsetᶜ 1) φ' hcyc
  have hz : capPairF X V 2 3 y φ' cc = 0 := by
    have hl := capPairF_leibniz X V 1 3 y hy ψ cc
    rw [scalarCastLeft_one_three] at hl
    have hψ' : (ψ.comp (singularBoundary ℚ X 1).hom) = φ' := hψ
    have hl' : capPairF X V 2 3 y φ' cc =
        capPairF X V 1 3 y ψ ((singularBoundary ℚ X 4).hom cc) := by
      rw [← hψ']; exact hl
    rw [hl']
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hcc
    rw [← huw, map_add,
      capPairF_eq_zero_of_front X V 1 3 y ψ (fun τ hτ => hψS _ (chainGenerator_mem_subChainSubmodule hτ)) hu,
      capPairF_eq_zero_of_back X V 1 3 y ψ hyv hw, add_zero]
  have hsplit : φ = φ' + φ₀.smulRight v := by
    simp [hφ']
  rw [hsplit, capPairF_add, LinearMap.add_apply, hz, zero_add, capPairF_smulRight]

open SphereOddDegree in
/-- **Cross relation** (Euclidean core of the locality argument).  If the relative `H₂` of `(X, X∖W)`
is spanned by `[a]`, `cc` is a relative 5-cycle of the triad `(X; X∖W, X∖Z)` and `y` is a
cocycle vanishing off `Z`, there is a universal scalar `r` with
`⟨y, φ ∩ cc⟩ = r • φ(a)` for every `V`-valued relative cocycle `φ`. -/
theorem cross_relation (Wset Zs : Set X) (y : (scalarChains X).X 3 →ₗ[ℚ] ℚ)
    (hy : ∀ e, y ((singularBoundary ℚ X 3).hom e) = 0)
    (hyv : ∀ τ : SingularSimplex X 3, IsSubordinate Zsᶜ τ → y (chainGenerator ℚ X 3 τ) = 0)
    (a : singularChainGroup ℚ X 2)
    (cc : singularChainGroup ℚ X 5)
    (hcc : (singularBoundary ℚ X 4).hom cc ∈
      subChainSubmodule ℚ X Wsetᶜ 4 ⊔ subChainSubmodule ℚ X Zsᶜ 4)
    (hspan : ∀ z : singularChainGroup ℚ X 2, (singularBoundary ℚ X 1).hom z ∈
      subChainSubmodule ℚ X Wsetᶜ 1 → ∃ (q : ℚ) (f : singularChainGroup ℚ X 3),
        z - q • a - (singularBoundary ℚ X 2).hom f ∈ subChainSubmodule ℚ X Wsetᶜ 2) :
    ∃ r : ℚ, ∀ (V : ModuleCat.{0} ℚ) (φ : singularChainGroup ℚ X 2 →ₗ[ℚ] V),
      (∀ τ : SingularSimplex X 2, IsSubordinate Wsetᶜ τ → φ (chainGenerator ℚ X 2 τ) = 0) →
      (∀ e, φ ((singularBoundary ℚ X 2).hom e) = 0) →
      capPairF X V 2 3 y φ cc = r • φ a := by
  let B' : Submodule ℚ (singularChainGroup ℚ X 2) :=
    subChainSubmodule ℚ X Wsetᶜ 2 ⊔ LinearMap.range (singularBoundary ℚ X 2).hom
  by_cases hB : a ∈ B'
  · refine ⟨0, fun V φ hφS hφd => ?_⟩
    obtain ⟨s, hs, w, ⟨e, rfl⟩, hsw⟩ := Submodule.mem_sup.mp hB
    have hφa : φ a = 0 := by
      rw [← hsw, map_add, vanish_on_sub X φ hφS hs, hφd, add_zero]
    have := cross_core X Wset Zs y hy hyv a cc hcc hspan V φ 0 0
      hφS hφd (fun _ _ => rfl) (fun _ => rfl) (by rw [hφa]; simp)
    rw [this, hφa]
    simp
  · obtain ⟨φ₀, hφ₀B, hφ₀a⟩ := LinearMap.exists_extend_of_notMem
      (p := B') (0 : B' →ₗ[ℚ] ℚ) hB (1 : ℚ)
    have hS : ∀ τ : SingularSimplex X 2, IsSubordinate Wsetᶜ τ → φ₀ (chainGenerator ℚ X 2 τ) = 0 := by
      intro τ hτ
      have hm : chainGenerator ℚ X 2 τ ∈ B' :=
        Submodule.mem_sup_left (chainGenerator_mem_subChainSubmodule hτ)
      have := LinearMap.congr_fun hφ₀B ⟨_, hm⟩
      simpa using this
    have hd : ∀ e, φ₀ ((singularBoundary ℚ X 2).hom e) = 0 := by
      intro e
      have hm : (singularBoundary ℚ X 2).hom e ∈ B' :=
        Submodule.mem_sup_right ⟨e, rfl⟩
      have := LinearMap.congr_fun hφ₀B ⟨_, hm⟩
      simpa using this
    refine ⟨capPairF X (ModuleCat.of ℚ ℚ) 2 3 y φ₀ cc, fun V φ hφS hφd => ?_⟩
    exact cross_core X Wset Zs y hy hyv a cc hcc hspan V φ φ₀ (φ a) hφS hφd hS hd
      (by rw [hφ₀a, one_smul])

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
