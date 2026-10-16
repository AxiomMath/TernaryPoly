module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Relative
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Absolute
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Descent

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCap
open CategoryTheory Limits
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SingularCoverNaturality
open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision

/-- Applying an actual chain or cochain map commutes with its actual differential. -/
theorem complexMap_d {c : ComplexShape ℕ} {K L : HomologicalComplex (ModuleCat.{0} ℚ) c}
    (q : K ⟶ L) (i j : ℕ) (x : K.X i) :
    L.d i j (q.f i x) = q.f j (K.d i j x) :=
  congrArg (fun f => f x) (q.comm i j)

/-- The cap degree relabelling is natural for every actual chain map. -/
theorem castLeft_map {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ}
    (q : K ⟶ L) (a b : ℕ) (x : K.X (a+b+1)) :
    (Descent.castLeft L a b).hom (q.f (a+b+1) x) =
      q.f (a+1+b) ((Descent.castLeft K a b).hom x) :=
  congrArg (fun f => f x) (HomologicalComplex.XIsoOfEq_hom_naturality q (show a+b+1 = a+1+b by omega))

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  [IsCancelSMul G E] [IsCancelSMul G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
  (hsquare : F ≫ p' = p ≫ f)
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
  (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) (V : Rep.{0} ℚ G)

omit [MulAction G E'] [ContinuousConstSMul G E'] [IsCancelSMul G E'] in
/-- The proved genuine cap identity expressed in the actual chain-complex differentials. -/
theorem cap_leibniz_complex :
    Descent.Leibniz (localCochains p hp V) (scalarChains B) (localChains p hp V) (capLinear p hp V) := by
  intro a b x c
  have h := cap_leibniz p hp V a b x c
  rw [scalarCastLeft_eq] at h
  have hd : (localCochains p hp V).d a (a+1) = ModuleCat.ofHom (differential p hp V a) := by
    simp [localCochains,CochainComplex.of_d]
  have hb : (localChains p hp V).d (b+1) b = ModuleCat.ofHom (boundary p hp V b) := by
    simp [localChains,ChainComplex.of_d]
  rw [hd,hb]
  exact h

/-- The actual relative cap satisfies the same signed Leibniz identity on every relative chain. -/
theorem relativeCap_leibniz : Descent.Leibniz (localCochains p' hp' V)
    (relativeScalarChains f) (relativeLocalChains p p' F hp hp' hF V)
    (relativeCap p p' F f hsquare hp hp' hF V) := by
  intro a b x c
  obtain ⟨c,rfl⟩ := RelativeAlgebra.projection_surjective (scalarSpaceMap f) (a+b+1) c
  rw [complexMap_d,castLeft_map]
  erw [relativeCap_projection,relativeCap_projection,relativeCap_projection,complexMap_d]
  have h := congrArg (fun z => (cokernel.π (localSpaceMap F hF V p p' hp hp')).f b z)
    (cap_leibniz_complex p' hp' V a b x c)
  simp only [map_add,map_zsmul] at h
  exact h

/-- The actual relative-cochain cap satisfies the signed Leibniz identity on every relative chain. -/
theorem relativeCochainCap_leibniz :
    Descent.Leibniz (relativeLocalCochains p p' F f hsquare hp hp' hF V)
      (relativeScalarChains f) (localChains p' hp' V)
      (relativeCochainCap p p' F f hsquare hp hp' hF V) := by
  intro a b x c
  obtain ⟨c,rfl⟩ := RelativeAlgebra.projection_surjective (scalarSpaceMap f) (a+b+1) c
  rw [complexMap_d,castLeft_map]
  erw [relativeCochainCap_projection,relativeCochainCap_projection,relativeCochainCap_projection]
  rw [← complexMap_d]
  exact cap_leibniz_complex p' hp' V a b
    ((kernel.ι (localPullback p p' F f hsquare hp hp' hF V)).f a x) c

/-- Absolute local cohomology acts on genuine relative scalar homology by the actual cap product. -/
def relativeCapHomology (a b : ℕ) :
    (localCochains p' hp' V).homology a →ₗ[ℚ]
      (relativeScalarChains f).homology (a+b) →ₗ[ℚ]
        (relativeLocalChains p p' F hp hp' hF V).homology b :=
  Descent.homology _ _ _ (relativeCap p p' F f hsquare hp hp' hF V)
    (relativeCap_leibniz p p' F f hsquare hp hp' hF V) a b

/-- Genuine relative local cohomology and relative scalar homology cap to absolute local homology. -/
def relativeCochainCapHomology (a b : ℕ) :
    (relativeLocalCochains p p' F f hsquare hp hp' hF V).homology a →ₗ[ℚ]
      (relativeScalarChains f).homology (a+b) →ₗ[ℚ] (localChains p' hp' V).homology b :=
  Descent.homology _ _ _ (relativeCochainCap p p' F f hsquare hp hp' hF V)
    (relativeCochainCap_leibniz p p' F f hsquare hp hp' hF V) a b

end TernaryPoly.SingularLocalCap
