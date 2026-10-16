module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Product

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCap
open CategoryTheory
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open scoped Classical Simplicial

/-- The degree relabelling used in the front-coboundary term is natural in actual spaces. -/
theorem projection_castLeft {X Y : TopCat.{0}} (f : X ⟶ Y) (a b : ℕ)
    (σ : SingularSimplex X (a+b+1)) :
    projection f (a+1+b) (awCastSimplex X a b σ) =
      awCastSimplex Y a b (projection f (a+b+1) σ) :=
  (ConcreteCategory.congr_hom ((TopCat.toSSet.map f).naturality (awCastLeft a b).op) σ).symm

/-- Actual singular faces commute with projection. -/
theorem projection_face {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (i : Fin (n+2)) (σ : SingularSimplex X (n+1)) :
    projection f n (faceSimplex X n i σ) =
      faceSimplex Y n i (projection f (n+1) σ) :=
  (ConcreteCategory.congr_hom ((TopCat.toSSet.map f).naturality (SimplexCategory.δ i).op) σ).symm

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  [IsCancelSMul G E] (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep.{0} ℚ G)

/-- The precise signed Leibniz formula for the actual cap of an actual projected simplex. -/
theorem capSimplex_leibniz_projected (a b : ℕ) (φ : VertexCochain p hp V a)
    (τ : SingularSimplex E (a+b+1)) :
    ∑ k : Fin (a+b+2), (-1 : ℤ)^k.val •
      capSimplex p hp V a b (faceSimplex B (a+b) k (projection p (a+b+1) τ)) φ =
      capSimplex p hp V (a+1) b (awCastSimplex B a b (projection p (a+b+1) τ))
        (differential p hp V a φ) +
      (-1 : ℤ)^a • boundary p hp V b
        (capSimplex p hp V a (b+1) (projection p (a+b+1) τ) φ) := by
  apply (degreeEquiv p hp V b).symm.injective
  simp only [map_sum, map_zsmul, map_add]
  have hleft (k : Fin (a+b+2)) :
      (degreeEquiv p hp V b).symm
        (capSimplex p hp V a b (faceSimplex B (a+b) k (projection p (a+b+1) τ)) φ) =
      generator G E V b (backSimplex E a b (faceSimplex E (a+b) k τ))
        (vertexToFunction p hp φ (frontSimplex E a b (faceSimplex E (a+b) k τ))) := by
    rw [← projection_face]
    exact capSimplex_lift p hp V a b φ ⟨_,rfl⟩
  simp_rw [hleft]
  have hfront := capSimplex_lift p hp V (a+1) b (differential p hp V a φ)
    (⟨awCastSimplex E a b τ, projection_castLeft p a b τ⟩ :
      Lifts p (awCastSimplex B a b (projection p (a+b+1) τ)))
  rw [hfront]
  have hboundary := LinearMap.congr_fun (degreeEquiv_symm_boundary p hp V b)
    (capSimplex p hp V a (b+1) (projection p (a+b+1) τ) φ)
  change (degreeEquiv p hp V b).symm (boundary p hp V b _) =
    (coinvariantChains G E V).d (b+1) b ((degreeEquiv p hp V (b+1)).symm _) at hboundary
  erw [hboundary, capSimplex_lift p hp V a (b+1) φ ⟨τ,rfl⟩,
    generator_boundary G E V b (backSimplex E a (b+1) τ),
    differential_vertexToFunction p hp V a φ (frontSimplex E (a+1) b (awCastSimplex E a b τ))]
  exact aw_signed_identity a b (vertexToFunction p hp φ) (generator G E V b) τ

/-- The literal singular-chain degree relabelling for the front-coboundary term. -/
def scalarCastLeft (X : TopCat.{0}) (a b : ℕ) :
    singularChainGroup ℚ X (a+b+1) →ₗ[ℚ] singularChainGroup ℚ X (a+1+b) :=
  ((singularChainSimplicialModule ℚ X).map (awCastLeft a b).op).hom

/-- The degree relabelling acts by the same genuine simplex relabelling on generators. -/
theorem scalarCastLeft_generator (X : TopCat.{0}) (a b : ℕ)
    (σ : SingularSimplex X (a+b+1)) :
    scalarCastLeft X a b (chainGenerator ℚ X (a+b+1) σ) =
      chainGenerator ℚ X (a+1+b) (awCastSimplex X a b σ) :=
  singularChainSimplicialModule_map_generator ℚ X (a+1+b) (a+b+1) (awCastLeft a b).op σ

/-- The actual scalar boundary formula with integer signs, matching local-chain conventions. -/
theorem scalarBoundary_generator (X : TopCat.{0}) (n : ℕ) (σ : SingularSimplex X (n+1)) :
    (singularBoundary ℚ X n).hom (chainGenerator ℚ X (n+1) σ) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • chainGenerator ℚ X n (faceSimplex X n i σ) := by
  rw [singularBoundary_chainGenerator_formula]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Int.cast_smul_eq_zsmul ℚ ((-1 : ℤ)^i.val), Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The full signed cap Leibniz rule on all actual scalar singular chains. -/
theorem cap_leibniz (a b : ℕ) (φ : VertexCochain p hp V a)
    (c : singularChainGroup ℚ B (a+b+1)) :
    cap p hp V a b φ ((singularBoundary ℚ B (a+b)).hom c) =
      cap p hp V (a+1) b (differential p hp V a φ) (scalarCastLeft B a b c) +
        (-1 : ℤ)^a • boundary p hp V b (cap p hp V a (b+1) φ c) := by
  have hh : (cap p hp V a b φ).comp (singularBoundary ℚ B (a+b)).hom =
      (cap p hp V (a+1) b (differential p hp V a φ)).comp (scalarCastLeft B a b) +
      (-1 : ℤ)^a • (boundary p hp V b).comp (cap p hp V a (b+1) φ) := by
    apply scalarChain_ext
    intro σ
    change cap p hp V a b φ ((singularBoundary ℚ B (a+b)).hom (chainGenerator ℚ B (a+b+1) σ)) =
      cap p hp V (a+1) b (differential p hp V a φ)
        (scalarCastLeft B a b (chainGenerator ℚ B (a+b+1) σ)) +
      (-1 : ℤ)^a • boundary p hp V b (cap p hp V a (b+1) φ (chainGenerator ℚ B (a+b+1) σ))
    rw [scalarBoundary_generator, scalarCastLeft_generator]
    simp only [map_sum, map_zsmul, cap_generator]
    erw [cap_generator p hp V a (b+1)]
    obtain ⟨τ,hτ⟩ := chosenLift p hp (a+b+1) σ
    rw [← hτ]
    exact capSimplex_leibniz_projected p hp V a b φ τ
  exact LinearMap.congr_fun hh c

/-- Solving Leibniz for the local boundary gives its precise (-1)^a adjunction sign. -/
theorem boundary_cap (a b : ℕ) (φ : VertexCochain p hp V a)
    (c : singularChainGroup ℚ B (a+b+1)) :
    boundary p hp V b (cap p hp V a (b+1) φ c) =
      (-1 : ℤ)^a • (cap p hp V a b φ ((singularBoundary ℚ B (a+b)).hom c) -
        cap p hp V (a+1) b (differential p hp V a φ) (scalarCastLeft B a b c)) := by
  have hs : (-1 : ℤ)^a * (-1 : ℤ)^a = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [cap_leibniz]
  simp only [add_sub_cancel_left, smul_smul, hs, one_zsmul]

end TernaryPoly.SingularLocalCap
