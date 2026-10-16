module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Basic
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Shapiro.Induction
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.RepresentationTheory.Homological.Resolution

@[expose] public section


noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison
open CategoryTheory Representation Finsupp
open RelativeShapiroInduction EquivariantSingularSmall

variable (G : Type) [Group G] {A : Type} [MulAction G A] (a : A)

abbrev stabilizer := MulAction.stabilizer G a
abbrev orbitLabels := Rep.ofMulAction ℚ G (MulAction.orbit G a)

/-- Literal induction coordinates, with inversion converting right to left cosets. -/
def inducedOrbitLinear : Rep.ind (stabilizer G a).subtype (Rep.trivial ℚ (stabilizer G a) ℚ) ≃ₗ[ℚ]
    orbitLabels G a :=
  (coordinatesEquiv (stabilizer G a) (Rep.trivial ℚ (stabilizer G a) ℚ)).trans
    ((Finsupp.domLCongr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (stabilizer G a))).trans
      ((Finsupp.domLCongr (MulAction.orbitEquivQuotientStabilizer G a).symm).trans
        (MonoidAlgebra.coeffLinearEquiv ℚ).symm))

def orbitPoint (g : G) : MulAction.orbit G a := ⟨g • a, g, rfl⟩

@[simp] theorem inducedOrbitLinear_mk (g : G) (r : ℚ) :
    inducedOrbitLinear G a (IndV.mk (stabilizer G a).subtype (Representation.trivial ℚ (stabilizer G a) ℚ) g r)=
      MonoidAlgebra.single (orbitPoint G a g⁻¹) r := by
  change (MonoidAlgebra.coeffLinearEquiv ℚ).symm
    (Finsupp.domLCongr (MulAction.orbitEquivQuotientStabilizer G a).symm
      (Finsupp.domLCongr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (stabilizer G a))
        (coordinates (stabilizer G a) (Rep.trivial ℚ (stabilizer G a) ℚ)
          (IndV.mk (stabilizer G a).subtype _ g r)))) = _
  rw [coordinates_mk]
  simp [coset, QuotientGroup.quotientRightRelEquivQuotientLeftRel, orbitPoint,
    MulAction.orbitEquivQuotientStabilizer, MonoidAlgebra.coeffLinearEquiv]
  rfl

/-- The induced trivial stabilizer representation is the actual orbit permutation module. -/
def inducedOrbitIso : Rep.ind (stabilizer G a).subtype (Rep.trivial ℚ (stabilizer G a) ℚ) ≅ orbitLabels G a :=
  Rep.mkIso { inducedOrbitLinear G a with
    isIntertwining' := fun g => by
      apply IndV.hom_ext
      intro x
      apply LinearMap.ext
      intro r
      change inducedOrbitLinear G a (Representation.ind (stabilizer G a).subtype
        (Representation.trivial ℚ (stabilizer G a) ℚ) g (IndV.mk _ _ x r))=
          (orbitLabels G a).ρ g (inducedOrbitLinear G a (IndV.mk _ _ x r))
      rw [Representation.ind_mk, inducedOrbitLinear_mk, inducedOrbitLinear_mk]
      rw [Representation.ofMulAction_single]
      congr 1
      apply Subtype.ext
      simp [orbitPoint, mul_inv_rev, mul_smul] }

/-- Each actual isotropy group supplies its genuine induced bar resolution. -/
def inducedOrbitResolution : ProjectiveResolution
    (Rep.ind (stabilizer G a).subtype (Rep.trivial ℚ (stabilizer G a) ℚ)) :=
  (Rep.indFunctor ℚ (stabilizer G a).subtype).mapProjectiveResolution
    (Rep.barResolution ℚ (stabilizer G a))

/-- The same genuine projective complex resolves the literal orbit-label module. -/
def orbitResolution : ProjectiveResolution (orbitLabels G a) where
  complex := (inducedOrbitResolution G a).complex
  projective := (inducedOrbitResolution G a).projective
  π := (inducedOrbitResolution G a).π ≫ (ChainComplex.single₀ (Rep ℚ G)).map (inducedOrbitIso G a).hom
  quasiIso := by infer_instance

/-- Frobenius reciprocity is an actual cochain isomorphism, with restricted coefficients. -/
def orbitShapiroIso (W : Rep.{0} ℚ G) :
    homCochains (orbitResolution G a).complex W ≅
      homCochains (Rep.barResolution ℚ (stabilizer G a)).complex (Rep.res (stabilizer G a).subtype W) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (Rep.indResHomEquiv (stabilizer G a).subtype _ W).toModuleIso) (fun _ _ _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro b
      rfl)

end TernaryPoly.BoundaryFaceResolutionComparison
