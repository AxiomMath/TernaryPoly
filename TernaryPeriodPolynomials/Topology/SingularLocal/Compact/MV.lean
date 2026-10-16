module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVColimitObjects
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVOpenMaps
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVDiagramExact
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVTransport

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace SingularLocalSupport
open EquivariantSingularSmall EquivariantSingularMayerVietoris

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [T2Space B]
  (U D : Opens B)

variable [LocallyCompactSpace B] (hUD : U ⊔ D = ⊤)

/-- The genuine compact-support Mayer–Vietoris connecting morphism from the filtered fixed-support LES. -/
def compactConnecting (n : ℕ) : compactCohomology p V n ⟶
    compactCohomology (restrictedProjection p (U ⊓ D : Opens B)) V (n+1) :=
  (unionColimitIso p V U D hUD n).inv ≫ colim.map (connectingTransformation p V U D n) ≫
    (intersectionColimitIso p V U D (n+1)).hom

/-- The genuine compact-support Mayer–Vietoris segment centered on the two opens. -/
def compactMiddleSegment (n : ℕ) : ShortComplex (ModuleCat ℚ) :=
  transportShortComplex ((diagramMiddleSegment p V U D n).map colim)
    (intersectionColimitIso p V U D n) (pairColimitIso p V U D n) (unionColimitIso p V U D hUD n)

/-- The genuine compact-support Mayer–Vietoris segment centered on ambient compact cohomology. -/
def compactAmbientSegment (n : ℕ) : ShortComplex (ModuleCat ℚ) :=
  transportShortComplex ((diagramUnionSegment p V U D n).map colim)
    (pairColimitIso p V U D n) (unionColimitIso p V U D hUD n) (intersectionColimitIso p V U D (n+1))

/-- The genuine compact-support Mayer–Vietoris segment centered on intersection cohomology in positive degree. -/
def compactIntersectionSegment (n : ℕ) : ShortComplex (ModuleCat ℚ) :=
  transportShortComplex ((diagramIntersectionSegment p V U D n).map colim)
    (unionColimitIso p V U D hUD n) (intersectionColimitIso p V U D (n+1)) (pairColimitIso p V U D (n+1))

/-- Compact-support Mayer–Vietoris is exact at the two open pieces in every degree. -/
theorem compactMiddleSegment_exact (n : ℕ) : (compactMiddleSegment p V U D hUD n).Exact :=
  ShortComplex.exact_of_iso (transportShortComplexIso _ _ _ _) (diagramMiddleSegment_colimit_exact p V U D n)

/-- Compact-support Mayer–Vietoris is exact at the ambient base in every degree. -/
theorem compactAmbientSegment_exact (n : ℕ) : (compactAmbientSegment p V U D hUD n).Exact :=
  ShortComplex.exact_of_iso (transportShortComplexIso _ _ _ _) (diagramUnionSegment_colimit_exact p V U D n)

/-- Compact-support Mayer–Vietoris is exact at the intersection in every positive degree. -/
theorem compactIntersectionSegment_exact (n : ℕ) : (compactIntersectionSegment p V U D hUD n).Exact :=
  ShortComplex.exact_of_iso (transportShortComplexIso _ _ _ _) (diagramIntersectionSegment_colimit_exact p V U D n)

/-- The first arrow in the actual compact-support LES is precisely the signed pair of open extensions. -/
theorem compactMiddleSegment_f (n : ℕ) : (compactMiddleSegment p V U D hUD n).f = compactDiagonal p V U D n := by
  change (intersectionColimitIso p V U D n).inv ≫ colim.map (diagonalTransformation p V U D n) ≫
    (pairColimitIso p V U D n).hom = _
  apply (cancel_epi (intersectionColimitIso p V U D n).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply colimit.hom_ext
  intro P
  erw [← Category.assoc,colimit.ι_map,Category.assoc,pairColimitIso_ι,← Category.assoc,intersectionColimitIso_ι]
  change fixedDiagonal p V (compactOpenImage U P.1) (compactOpenImage D P.2) n ≫ _ = _
  exact fixedDiagonal_classInOpen p V U D (compactOpenImage U P.1) (compactOpenImage D P.2)
    (compactOpenImage_subset U P.1) (compactOpenImage_subset D P.2) n

/-- The second arrow in the actual compact-support LES is precisely the sum of open extensions. -/
theorem compactMiddleSegment_g (n : ℕ) : (compactMiddleSegment p V U D hUD n).g = compactSum p V U D n := by
  change (pairColimitIso p V U D n).inv ≫ colim.map (sumTransformation p V U D n) ≫
    (unionColimitIso p V U D hUD n).hom = _
  apply (cancel_epi (pairColimitIso p V U D n).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply colimit.hom_ext
  intro P
  erw [← Category.assoc,colimit.ι_map,Category.assoc,unionColimitIso_ι,← Category.assoc,pairColimitIso_ι]
  change fixedSum p V (compactOpenImage U P.1) (compactOpenImage D P.2) n ≫ _ = _
  exact fixedSum_classInOpen p V U D (compactOpenImage U P.1) (compactOpenImage D P.2)
    (compactOpenImage_subset U P.1) (compactOpenImage_subset D P.2) n

/-- Adjacent compact-support segments have the same actual open-extension sum. -/
theorem compactAmbientSegment_f (n : ℕ) : (compactAmbientSegment p V U D hUD n).f = compactSum p V U D n :=
  compactMiddleSegment_g p V U D hUD n

/-- The ambient segment retains the genuine colimit connecting morphism. -/
theorem compactAmbientSegment_g (n : ℕ) : (compactAmbientSegment p V U D hUD n).g = compactConnecting p V U D hUD n := rfl

/-- The intersection segment retains the same genuine connecting morphism. -/
theorem compactIntersectionSegment_f (n : ℕ) : (compactIntersectionSegment p V U D hUD n).f = compactConnecting p V U D hUD n := rfl

/-- The intersection segment retains the signed open-extension diagonal in the next degree. -/
theorem compactIntersectionSegment_g (n : ℕ) : (compactIntersectionSegment p V U D hUD n).g = compactDiagonal p V U D (n+1) :=
  compactMiddleSegment_f p V U D hUD (n+1)

include hUD in
/-- The actual signed open-extension map is injective in degree zero. -/
theorem compactDiagonal_zero_mono : Mono (compactDiagonal p V U D 0) := by
  have : ∀ P : Compacts U × Compacts D, Mono ((diagonalTransformation p V U D 0).app P) := fun P =>
    fixedDiagonal_zero_mono p V (compactOpenImage U P.1) (compactOpenImage D P.2)
      (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed
  have : Mono (diagonalTransformation p V U D 0) := NatTrans.mono_of_mono_app _
  rw [← compactMiddleSegment_f p V U D hUD 0]
  change Mono ((intersectionColimitIso p V U D 0).inv ≫ colim.map (diagonalTransformation p V U D 0) ≫
    (pairColimitIso p V U D 0).hom)
  infer_instance

/-- The genuine connecting morphism retains the fixed-support connecting map on every actual compact pair. -/
theorem compactConnecting_classMap (n : ℕ) (P : Compacts U × Compacts D) :
    compactClassMap p V (compactUnion U D P) n ≫ compactConnecting p V U D hUD n =
      fixedConnecting p V (compactOpenImage U P.1) (compactOpenImage D P.2)
        (compactOpenImage U P.1).isCompact.isClosed (compactOpenImage D P.2).isCompact.isClosed n ≫
          classInOpen p V (U ⊓ D) (compactIntersection U D P) (compactIntersection_subset U D P) (n+1) := by
  have h := colimitTransport_ι (unionColimitIso p V U D hUD n) (intersectionColimitIso p V U D (n+1))
    (connectingTransformation p V U D n) P
  rw [unionColimitIso_ι,intersectionColimitIso_ι] at h
  exact h

end TernaryPoly.SingularLocalCompactMV
