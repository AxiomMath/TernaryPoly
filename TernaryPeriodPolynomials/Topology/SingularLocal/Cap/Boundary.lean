module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.BoundaryClasses

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCap
open CategoryTheory Limits
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SingularCoverNaturality BoundaryClasses
open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision

/-- The represented linear family of an integer multiple is the same integer multiple of the family. -/
theorem elementMap_zsmul {M : ModuleCat.{0} ℚ} (x : M) (r : ℤ) :
    elementMap (r • x) = r • elementMap x := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  exact smul_comm q r x

/-- A Koszul multiple is a cycle precisely when the original family is a cycle. -/
theorem cycle_of_signed_cycle (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) (n a : ℕ)
    {A : ModuleCat.{0} ℚ} (x : A ⟶ K.X n)
    (hx : ((-1 : ℤ)^a • x) ≫ K.d n (n-1) = 0) : x ≫ K.d n (n-1) = 0 := by
  have hs : (-1 : ℤ)^a * (-1 : ℤ)^a = 1 := by
    rw [← pow_add,← two_mul,pow_mul]; norm_num
  rw [Preadditive.zsmul_comp] at hx
  have h := congrArg (fun z => (-1 : ℤ)^a • z) hx
  simpa only [smul_smul,hs,one_zsmul,smul_zero] using h

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  [IsCancelSMul G E] [IsCancelSMul G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
  (hsquare : F ≫ p' = p ≫ f)
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
  (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) (V : Rep.{0} ℚ G)

/-- The boundary of a cocycle cap is the signed pushforward of its restriction capped with the lifted boundary. -/
theorem cap_boundary_of_lift (a b : ℕ) (φ : VertexCochain p' hp' V a)
    (hφ : differential p' hp' V a φ = 0)
    (c : singularChainGroup ℚ B' (a+b+1)) (z : singularChainGroup ℚ B (a+b))
    (hc : (singularBoundary ℚ B' (a+b)).hom c = (scalarSpaceMap f).f (a+b) z) :
    boundary p' hp' V b (cap p' hp' V a (b+1) φ c) =
      (-1 : ℤ)^a • (localSpaceMap F hF V p p' hp hp').f b
        (cap p hp V a b (vertexPullback p p' F f hsquare hp hp' hF V a φ) z) := by
  rw [boundary_cap,hφ,hc]
  change (-1 : ℤ)^a • (_ - capLinear p' hp' V (a+1) b 0 _) = _
  rw [map_zero,LinearMap.zero_apply,sub_zero]
  exact congrArg (fun w => (-1 : ℤ)^a • w)
    (cap_natural p p' F f hsquare hp hp' hF V a b φ z).symm

/-- The actual cocycle cap and its signed boundary cap give the diagram used by the genuine connecting map. -/
theorem cap_boundary_diagram (a b : ℕ) (φ : VertexCochain p' hp' V a)
    (hφ : differential p' hp' V a φ = 0)
    (c : singularChainGroup ℚ B' (a+b+1)) (z : singularChainGroup ℚ B (a+b))
    (hc : (singularBoundary ℚ B' (a+b)).hom c = (scalarSpaceMap f).f (a+b) z) :
    ((-1 : ℤ)^a • elementMap (M := (localChains p hp V).X b)
      (cap p hp V a b (vertexPullback p p' F f hsquare hp hp' hF V a φ) z)) ≫
        (localSpaceMap F hF V p p' hp hp').f b =
      elementMap (M := (localChains p' hp' V).X (b+1)) (cap p' hp' V a (b+1) φ c) ≫
        (localChains p' hp' V).d (b+1) b := by
  erw [Preadditive.zsmul_comp,elementMap_comp,elementMap_comp,← elementMap_zsmul]
  apply congrArg elementMap
  have h := cap_boundary_of_lift p p' F f hsquare hp hp' hF V a b φ hφ c z hc
  have hb : (localChains p' hp' V).d (b+1) b = ModuleCat.ofHom (boundary p' hp' V b) := by
    simp [localChains,ChainComplex.of_d]
  rw [hb]
  exact h.symm

/-- The actual relative connecting homomorphism has exactly the (-1)^a cap boundary sign.
The two witnesses are cycle proofs, not geometric assumptions or duality oracles. -/
theorem connecting_cap [Mono (localSpaceMap F hF V p p' hp hp')]
    (a b : ℕ) (φ : VertexCochain p' hp' V a) (hφ : differential p' hp' V a φ = 0)
    (c : singularChainGroup ℚ B' (a+b+1)) (z : singularChainGroup ℚ B (a+b))
    (hc : (singularBoundary ℚ B' (a+b)).hom c = (scalarSpaceMap f).f (a+b) z) :
    let x₂ := elementMap (M := (localChains p' hp' V).X (b+1)) (cap p' hp' V a (b+1) φ c)
    let x₁ := elementMap (M := (localChains p hp V).X b)
      (cap p hp V a b (vertexPullback p p' F f hsquare hp hp' hF V a φ) z)
    let i := localSpaceMap F hF V p p' hp hp'
    ∃ (h₂ : (x₂ ≫ (cokernel.π i).f (b+1)) ≫ (cokernel i).d (b+1) (b+1-1) = 0)
      (h₁ : x₁ ≫ (localChains p hp V).d b (b-1) = 0),
      classMap (cokernel i) (b+1) (x₂ ≫ (cokernel.π i).f (b+1)) h₂ ≫
        RelativeChainSequence.connecting i b = (-1 : ℤ)^a • classMap (localChains p hp V) b x₁ h₁ := by
  dsimp only
  let x₂ := elementMap (M := (localChains p' hp' V).X (b+1)) (cap p' hp' V a (b+1) φ c)
  let x₁ := elementMap (M := (localChains p hp V).X b)
    (cap p hp V a b (vertexPullback p p' F f hsquare hp hp' hF V a φ) z)
  let i := localSpaceMap F hF V p p' hp hp'
  have hd := cap_boundary_diagram p p' F f hsquare hp hp' hF V a b φ hφ c z hc
  have h₂ := projected_cycle i b x₂ ((-1 : ℤ)^a • x₁) hd
  have h₁s := lifted_boundary_cycle i b x₂ ((-1 : ℤ)^a • x₁) hd
  have h₁ := cycle_of_signed_cycle (localChains p hp V) b a x₁ h₁s
  refine ⟨h₂,h₁,?_⟩
  exact (connecting_classMap i b x₂ ((-1 : ℤ)^a • x₁) hd).trans
    (classMap_zsmul (localChains p hp V) b x₁ h₁ ((-1 : ℤ)^a) h₁s)

end TernaryPoly.SingularLocalCap
