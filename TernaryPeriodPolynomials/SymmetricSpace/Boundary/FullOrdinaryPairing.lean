module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullOrdinaryComparison

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory HomologicalComplex EquivariantSingularSmall OrdinaryParabolicGroups OrdinaryBoundaryCone
open Representation

variable (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL)

def geometricOrdinary0 (c : fullBoundaryChains.X 0 ⟶ W) : C0 W :=
  ordinaryCoordinates0 W (canonicalBoundaryEquiv.inv.f 0 ≫ c)

def geometricOrdinary1 (c : fullBoundaryChains.X 1 ⟶ W) : C1 W P Q :=
  ordinaryCoordinates1 W (canonicalBoundaryEquiv.inv.f 1 ≫ c)

def geometricOrdinary2 (c : fullBoundaryChains.X 2 ⟶ W) : C2 W P Q :=
  ordinaryCoordinates2 W (canonicalBoundaryEquiv.inv.f 2 ≫ c)

/-- Actual full-boundary chain represented by an identity-induced plane bar generator. -/
def geometricPlaneGenerator (g : P) : fullBoundaryChains.X 1 :=
  (canonicalBoundaryEquiv.inv.f 1).hom
    ((signedPlaneInclusion canonicalLineArrow canonicalPlaneArrow 1).hom
      (IndV.mk P.subtype ((Rep.barResolution ℚ P).complex.X 1).ρ 1
        (Finsupp.single (fun _ => g) (MonoidAlgebra.single 1 1))))

def geometricLineGenerator (g : Q) : fullBoundaryChains.X 1 :=
  (canonicalBoundaryEquiv.inv.f 1).hom
    ((signedLineInclusion canonicalLineArrow canonicalPlaneArrow 1).hom
      (IndV.mk Q.subtype ((Rep.barResolution ℚ Q).complex.X 1).ρ 1
        (Finsupp.single (fun _ => g) (MonoidAlgebra.single 1 1))))

/-- The corner generator before the ordinary sign conversion. -/
def geometricCornerGenerator : fullBoundaryChains.X 1 :=
  (canonicalBoundaryEquiv.inv.f 1).hom
    ((signedCornerInclusion canonicalLineArrow canonicalPlaneArrow 0).hom
      (IndV.mk B.subtype ((Rep.barResolution ℚ B).complex.X 0).ρ 1
        (Finsupp.single default (MonoidAlgebra.single 1 1))))

/-- Ordinary coordinates are literal evaluation on actual full-boundary chains. -/
theorem geometricOrdinary1_evaluation (c : fullBoundaryChains.X 1 ⟶ W) :
    geometricOrdinary1 W c = (fun g => c.hom (geometricPlaneGenerator g),
      (fun g => c.hom (geometricLineGenerator g)), -c.hom geometricCornerGenerator) := by
  unfold geometricOrdinary1
  rw [ordinaryCoordinates1_apply]
  apply Prod.ext
  · funext g
    exact inducedCoordinates1_apply P W _ g
  apply Prod.ext
  · funext g
    exact inducedCoordinates1_apply Q W _ g
  · exact congrArg Neg.neg (inducedCoordinates0_apply B W _)

/-- The finite-chain pairing evaluates genuine geometric boundary chains with the exact corner sign. -/
theorem geometric_pair1_evaluation (c : fullBoundaryChains.X 1 ⟶ W) (z : Chains1 W P Q) :
    pair1 W P Q (geometricOrdinary1 W c) z =
      barPair (fun g => c.hom (geometricPlaneGenerator g)) z.1 +
      barPair (fun g => c.hom (geometricLineGenerator g)) z.2.1 -
      z.2.2 (c.hom geometricCornerGenerator) := by
  rw [geometricOrdinary1_evaluation]
  change _ + _ + z.2.2 (-c.hom geometricCornerGenerator) = _
  rw [map_neg,sub_eq_add_neg]

theorem geometricOrdinary_d0 (c : fullBoundaryChains.X 0 ⟶ W) :
    geometricOrdinary1 W (fullBoundaryChains.d 1 0 ≫ c) = d0 W P Q (geometricOrdinary0 W c) := by
  unfold geometricOrdinary1 geometricOrdinary0
  have h := canonicalBoundaryEquiv.inv.comm 1 0
  have he : canonicalBoundaryEquiv.inv.f 1 ≫ fullBoundaryChains.d 1 0 ≫ c =
      canonicalFaceCone.d 1 0 ≫ canonicalBoundaryEquiv.inv.f 0 ≫ c :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ c) h).trans (Category.assoc _ _ _))
  exact (congrArg (ordinaryCoordinates1 W) he).trans (ordinaryCoordinates_d0 W _)

theorem geometricOrdinary_d1 (c : fullBoundaryChains.X 1 ⟶ W) :
    geometricOrdinary2 W (fullBoundaryChains.d 2 1 ≫ c) = d1 W P Q (geometricOrdinary1 W c) := by
  unfold geometricOrdinary2 geometricOrdinary1
  have h := canonicalBoundaryEquiv.inv.comm 2 1
  have he : canonicalBoundaryEquiv.inv.f 2 ≫ fullBoundaryChains.d 2 1 ≫ c =
      canonicalFaceCone.d 2 1 ≫ canonicalBoundaryEquiv.inv.f 1 ≫ c :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ c) h).trans (Category.assoc _ _ _))
  exact (congrArg (ordinaryCoordinates2 W) he).trans (ordinaryCoordinates_d1 W _)

/-- Degree-zero adjunction for actual geometric cochains and all finite ordinary cone chains. -/
theorem geometric_pair_adjunction0 (c : fullBoundaryChains.X 0 ⟶ W) (z : Chains1 W P Q) :
    pair1 W P Q (geometricOrdinary1 W (fullBoundaryChains.d 1 0 ≫ c)) z =
    pair0 W (geometricOrdinary0 W c) (chainBoundary1 W P Q z) := by
  rw [geometricOrdinary_d0]
  exact cone_adjunction0 W P Q _ z

/-- Degree-one adjunction preserves the actual face restrictions and shifted corner term. -/
theorem geometric_pair_adjunction1 (c : fullBoundaryChains.X 1 ⟶ W) (z : Chains2 W P Q) :
    pair2 W P Q (geometricOrdinary2 W (fullBoundaryChains.d 2 1 ≫ c)) z =
    pair1 W P Q (geometricOrdinary1 W c) (chainBoundary2 W P Q z) := by
  rw [geometricOrdinary_d1]
  exact cone_adjunction1 W P Q _ z

/-- A genuine entire-boundary cocycle pulls back to a literal ordinary cone cocycle. -/
def geometricOrdinaryCycle (c : fullBoundaryChains.X 1 ⟶ W)
    (hc : fullBoundaryChains.d 2 1 ≫ c = 0) : Z1 W P Q :=
  ⟨geometricOrdinary1 W c,by
    change d1 W P Q (geometricOrdinary1 W c) = 0
    rw [←geometricOrdinary_d1,hc]
    unfold geometricOrdinary2
    rw [Limits.comp_zero,map_zero]⟩

/-- Pairwise normalization preserves evaluation of an actual geometric cocycle on every
finite ordinary cone cycle, including the actual corner evaluation and sign. -/
theorem geometric_pairwise_normalized_pairing (n : ℕ) (e : ℤ)
    (c : fullBoundaryChains.X 1 ⟶ actualCoefficients n e)
    (hc : fullBoundaryChains.d 2 1 ≫ c = 0) :
    ∃ c' : actualCycles n e,
      classOf (actualCoefficients n e) P Q c' =
        classOf (actualCoefficients n e) P Q (geometricOrdinaryCycle (actualCoefficients n e) c hc) ∧
      (∀ g : P, Pairwise (OrdinaryBoundaryCommonRoot.evaluation n (c'.val.1 g) : PolynomialGLAction.Poly)) ∧
      (∀ g : Q, Pairwise (OrdinaryBoundaryCommonRoot.evaluation n (c'.val.2.1 g) : PolynomialGLAction.Poly)) ∧
      Pairwise (OrdinaryBoundaryCommonRoot.evaluation n c'.val.2.2 : PolynomialGLAction.Poly) ∧
      ∀ z : actualChains n e, chainBoundary1 (actualCoefficients n e) P Q z = 0 →
        pair1 (actualCoefficients n e) P Q c'.val z =
          pair1 (actualCoefficients n e) P Q (geometricOrdinary1 (actualCoefficients n e) c) z := by
  obtain ⟨c',hclass,hp,hq,hb⟩ := actual_class_pairwise_representative n e
    (classOf (actualCoefficients n e) P Q (geometricOrdinaryCycle (actualCoefficients n e) c hc))
  refine ⟨c',hclass,hp,hq,hb,?_⟩
  obtain ⟨v,hv⟩ := (classOf_eq_iff (actualCoefficients n e) P Q c'
    (geometricOrdinaryCycle (actualCoefficients n e) c hc)).mp hclass
  intro z hz
  rw [hv]
  exact gauge_pair_cycle (actualCoefficients n e) P Q _ v z hz

end TernaryPoly.SymmetricSpaceBoundaryFull
