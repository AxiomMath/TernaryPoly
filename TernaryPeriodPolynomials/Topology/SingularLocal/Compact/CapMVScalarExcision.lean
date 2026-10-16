module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVSmall
public import TernaryPeriodPolynomials.Topology.Rational.Local.OrientationSupport

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SphereOddDegree RationalRelativeSingular RationalRelativeExcision RationalLocalOrientation

/-- A quotient map of actual chain monomorphisms is monic when its first comparison is epi
and its second comparison is mono. -/
theorem cokernelMap_mono {K L K' L' : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (i : K ⟶ L) (i' : K' ⟶ L') [Mono i] [Mono i']
    (f : K ⟶ K') (g : L ⟶ L') (h : i ≫ g = f ≫ i') [Epi f] [Mono g] :
    Mono (cokernel.map i i' f g h) := by
  let φ : RelativeChainSequence.sequence i ⟶ RelativeChainSequence.sequence i' :=
    { τ₁ := f
      τ₂ := g
      τ₃ := cokernel.map i i' f g h
      comm₁₂ := h.symm
      comm₂₃ := by simp [RelativeChainSequence.sequence,cokernel.map] }
  exact ShortComplex.mono_of_epi_of_epi_of_mono φ
    (RelativeChainSequence.shortExact i').exact
    (inferInstanceAs (Epi (cokernel.π i))) (inferInstanceAs (Epi f)) (inferInstanceAs (Mono g))

/-- The scalar small-relative comparison for a two-open cover is injective on chains. -/
instance scalarTwoOpenSmallMap_mono {X : Type} [TopologicalSpace X]
    (U D : Opens X) (hUD : U ⊔ D = ⊤) : Mono (RationalRelativeExcision.smallRelativeMap U D hUD) := by
  have hm : Mono (smallChainsInclusion ℚ (TopCat.of X) (twoSetCover U D hUD)) := by
    apply mono_of_mono_f
    intro n
    exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  exact @cokernelMap_mono _ _ _ _ (mvInclU_small ℚ (X := TopCat.of X) U D hUD)
    (inclusion (U : Set X)) inferInstance inferInstance (inv (subChainCorestrict ℚ (TopCat.of X) U))
    (smallChainsInclusion ℚ (TopCat.of X) (twoSetCover U D hUD)) (smallToFull_square U D hUD) inferInstance hm

/-- The actual excision inclusion for a closed support in an open neighborhood is monic on chains. -/
theorem scalarSupportExcision_mono {X : Type} [TopologicalSpace X]
    (K : Set X) (hK : IsClosed K) (U : Opens X) (hKU : K ⊆ U) :
    Mono (supportExcisionMap K U) := by
  let D : Opens X := ⟨Kᶜ,hK.isOpen_compl⟩
  have hDU : D ⊔ U = ⊤ := by
    ext x
    change (x ∈ Kᶜ ∨ x ∈ U) ↔ True
    simp only [iff_true]
    by_cases hx : x ∈ K
    · exact Or.inr (hKU hx)
    · exact Or.inl hx
  change Mono (excisionMap (D : Set X) (U : Set X))
  rw [excisionMap_factorization D U hDU]
  infer_instance

/-- A refinement of actual open covers induces the literal inclusion of small chains. -/
def smallRefine {X : TopCat.{0}} (𝒰 𝒱 : OpenCoverData X)
    (hUV : ∀ n (σ : singularSimplices X n), IsSmallSimplex 𝒰 σ → IsSmallSimplex 𝒱 σ) :
    smallChainComplex ℚ X 𝒰 ⟶ smallChainComplex ℚ X 𝒱 where
  f n := ModuleCat.ofHom (Submodule.inclusion (by
    apply Submodule.span_le.mpr
    rintro _ ⟨σ,hσ,rfl⟩
    exact chainGenerator_mem_smallChainSubmodule (hUV n σ hσ)))
  comm' i j hij := by
    obtain rfl : i = j+1 := hij.symm
    simp only [smallChainComplex_d]
    rfl

/-- The actual refinement retains each scalar chain. -/
theorem smallRefine_inclusion {X : TopCat.{0}} (𝒰 𝒱 : OpenCoverData X)
    (hUV : ∀ n (σ : singularSimplices X n), IsSmallSimplex 𝒰 σ → IsSmallSimplex 𝒱 σ) :
    smallRefine 𝒰 𝒱 hUV ≫ smallChainsInclusion ℚ X 𝒱 = smallChainsInclusion ℚ X 𝒰 := by
  ext n c
  rfl

/-- The actual two-open cover formed by a support complement and its open neighborhood. -/
def supportOpenCover {X : TopCat.{0}} (K : Set X) (hK : IsClosed K)
    (U : Opens X) (hKU : K ⊆ U) : OpenCoverData X :=
  twoSetCover ⟨Kᶜ,hK.isOpen_compl⟩ U (by
    ext x
    change (x ∈ Kᶜ ∨ x ∈ U) ↔ True
    simp only [iff_true]
    by_cases hx : x ∈ K
    · exact Or.inr (hKU hx)
    · exact Or.inl hx)

/-- A sufficiently small scalar chain localizes canonically to the actual relative support
chains of an open neighborhood, by the actual small-chain excision isomorphism. -/
def localizeSmallScalar {X : TopCat.{0}} (K : Set X) (hK : IsClosed K)
    (U : Opens X) (hKU : K ⊆ U) (𝒰 : OpenCoverData X)
    (href : ∀ n (σ : singularSimplices X n), IsSmallSimplex 𝒰 σ →
      IsSmallSimplex (supportOpenCover K hK U hKU) σ) :
    smallChainComplex ℚ X 𝒰 ⟶ relativeChains ((Subtype.val : U → X) ⁻¹' K)ᶜ := by
  let D : Opens X := ⟨Kᶜ,hK.isOpen_compl⟩
  have hDU : D ⊔ U = ⊤ := by
    ext x
    change (x ∈ Kᶜ ∨ x ∈ U) ↔ True
    simp only [iff_true]
    by_cases hx : x ∈ K
    · exact Or.inr (hKU hx)
    · exact Or.inl hx
  exact smallRefine 𝒰 (supportOpenCover K hK U hKU) href ≫
    cokernel.π (mvInclU_small ℚ (X := X) D U hDU) ≫
      (asIso (supportedSmallMap D U hDU)).inv ≫ (asIso (insideRelativeMap D U)).inv

/-- The actual scalar localization retains the ambient relative scalar chain exactly. -/
theorem localizeSmallScalar_excision {X : TopCat.{0}} (K : Set X) (hK : IsClosed K)
    (U : Opens X) (hKU : K ⊆ U) (𝒰 : OpenCoverData X)
    (href : ∀ n (σ : singularSimplices X n), IsSmallSimplex 𝒰 σ →
      IsSmallSimplex (supportOpenCover K hK U hKU) σ) :
    localizeSmallScalar K hK U hKU 𝒰 href ≫ supportExcisionMap K U =
      smallChainsInclusion ℚ X 𝒰 ≫ cokernel.π (inclusion Kᶜ) := by
  let D : Opens X := ⟨Kᶜ,hK.isOpen_compl⟩
  have hDU : D ⊔ U = ⊤ := by
    ext x
    change (x ∈ Kᶜ ∨ x ∈ U) ↔ True
    simp only [iff_true]
    by_cases hx : x ∈ K
    · exact Or.inr (hKU hx)
    · exact Or.inl hx
  change (smallRefine 𝒰 (supportOpenCover K hK U hKU) href ≫
    cokernel.π (mvInclU_small ℚ (X := X) D U hDU) ≫
      (asIso (supportedSmallMap D U hDU)).inv ≫ (asIso (insideRelativeMap D U)).inv) ≫
        excisionMap (D : Set X) (U : Set X) = _
  rw [excisionMap_factorization D U hDU]
  simp only [asIso_inv]
  erw [Category.assoc,Category.assoc,Category.assoc,IsIso.inv_hom_id_assoc,IsIso.inv_hom_id_assoc]
  simp only [RationalRelativeExcision.smallRelativeMap,cokernel.map]
  erw [cokernel.π_desc]
  erw [← Category.assoc]

end TernaryPoly.SingularLocalCompactCapMV
