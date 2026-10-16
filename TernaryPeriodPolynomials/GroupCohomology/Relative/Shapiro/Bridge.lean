module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Shapiro.Induction
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Shapiro.Comparison
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Shapiro.Modules

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeShapiroBridge
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open Representation Finsupp
open RelativeShapiroModules RelativeShapiroInduction RelativeExtObstructionSequences

variable (H : Subgroup K)

/-- Induction of the trivial module is the actual untwisted left-coset module.
Inversion changes Mathlib's right-coset induction convention to left translation. -/
def inducedTrivialLinear : Rep.ind H.subtype (Rep.trivial ℚ H ℚ) ≃ₗ[ℚ] ((K ⧸ H) →₀ ℚ) :=
  (coordinatesEquiv H (Rep.trivial ℚ H ℚ)).trans
    (Finsupp.domLCongr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H))

@[simp]
lemma inducedTrivialLinear_mk (g : K) (a : ℚ) :
    inducedTrivialLinear H (IndV.mk H.subtype (Representation.trivial ℚ H ℚ) g a) =
      Finsupp.single (QuotientGroup.mk g⁻¹ : K ⧸ H) a := by
  change Finsupp.domLCongr (R := ℚ)
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)
      (coordinates H (Rep.trivial ℚ H ℚ)
        (IndV.mk H.subtype (Rep.trivial ℚ H ℚ).ρ g a)) = _
  rw [coordinates_mk]
  simp [coset, QuotientGroup.quotientRightRelEquivQuotientLeftRel]

/-- The induced trivial object and the literal coset representation are isomorphic in Rep. -/
def inducedTrivialIso : Rep.ind H.subtype (Rep.trivial ℚ H ℚ) ≅ CosetRep H :=
  Rep.mkIso { inducedTrivialLinear H with
    isIntertwining' := fun g => by
      apply IndV.hom_ext
      intro x
      apply LinearMap.ext
      intro a
      change inducedTrivialLinear H (Representation.ind H.subtype
        (Representation.trivial ℚ H ℚ) g (IndV.mk H.subtype _ x a)) =
          (CosetRep H).ρ g (inducedTrivialLinear H (IndV.mk H.subtype _ x a))
      rw [Representation.ind_mk, inducedTrivialLinear_mk, inducedTrivialLinear_mk]
      simp [cosetAction, RelativeOrbitCosets.cosetLinear, mul_inv_rev] }

/-- Frobenius reciprocity identifies the genuine complexes calculating Ext. -/
def inducedResolutionHomIso (P : ProjectiveResolution (Rep.trivial ℚ H ℚ))
    (E : Rep.{0} ℚ K) :
    ((Rep.indFunctor ℚ H.subtype).mapProjectiveResolution P).complex.linearYonedaObj ℚ E ≅
      P.complex.linearYonedaObj ℚ (Rep.res H.subtype E) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (Rep.indResHomEquiv H.subtype _ E).toModuleIso) (fun _ _ _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro a
      rfl)

/-- Genuine additive Ext–Shapiro in every positive degree, for the actual coefficient restriction. -/
def cosetExtEquivGroupCohomology (E : Rep.{0} ℚ K) (n : ℕ) :
    Ext.{1} (CosetRep H) E (n + 1) ≃+
      groupCohomology (Rep.res H.subtype E) (n + 1) :=
  (RelativeShapiroComparison.extCongrLeft (inducedTrivialIso H) (n + 1)).trans
    ((RelativeShapiroComparison.extEquivResolutionHomology ℚ
      ((Rep.indFunctor ℚ H.subtype).mapProjectiveResolution (Rep.barResolution ℚ H)) n).trans
        (((HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso
          (inducedResolutionHomIso H (Rep.barResolution ℚ H) E) ≪≫
            (groupCohomologyIso (Rep.res H.subtype E) (n + 1) (Rep.barResolution ℚ H)).symm).toLinearEquiv.toAddEquiv))

/-- Genuine Ext–Shapiro vanishing in every positive degree, with actual restriction. -/
theorem coset_ext_subsingleton (E : Rep.{0} ℚ K) (n : ℕ)
    (h : IsZero (groupCohomology (Rep.res H.subtype E) (n + 1))) :
    Subsingleton (Ext.{1} (CosetRep H) E (n + 1)) := by
  let P := Rep.barResolution ℚ H
  let PI := (Rep.indFunctor ℚ H.subtype).mapProjectiveResolution P
  have hP : IsZero ((P.complex.linearYonedaObj ℚ (Rep.res H.subtype E)).homology (n + 1)) :=
    h.of_iso (groupCohomologyIso (Rep.res H.subtype E) (n + 1) P).symm
  have hPI : IsZero ((PI.complex.linearYonedaObj ℚ E).homology (n + 1)) :=
    hP.of_iso ((HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso
      (inducedResolutionHomIso H P E))
  have : Subsingleton (Ext.{1} (Rep.ind H.subtype (Rep.trivial ℚ H ℚ)) E (n + 1)) :=
    RelativeShapiroExt.ext_subsingleton_of_resolution_homology ℚ PI n hPI
  exact ext_subsingleton_of_iso (inducedTrivialIso H) (n + 1)

end TernaryPoly.RelativeShapiroBridge
