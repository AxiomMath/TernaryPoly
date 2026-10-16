module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EdgeControl.Controlled
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PlaneLevelCocycle

@[expose] public section


/-!
# Control of the source group cocycle on the real plane group

The plane group cocycle of a plane source cocycle is, at a pair `(p, q)` of real plane group
elements, the source on the simplex `(1, P, P Q)`. Its real translates are, monomial by monomial,
the source-cochain cusp vectors at the translated argument, whose bounded realizations depend
continuously on the vertices and the argument. Hence the plane group cocycle along continuous
paths is a controlled family.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.EdgeControl

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem continuous_planeLeviOne : Continuous (fun B : BinaryRealGL => planeLevi B 1) := by
  apply Units.continuous_iff.mpr
  have block (f : BinaryRealGL → Matrix (Fin 2) (Fin 2) ℝ) (hf : Continuous f) :
      Continuous (fun B => planeBlock (f B) (1 : ℝ)) := by
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    fin_cases row <;> fin_cases column <;> simp [planeBlock] <;>
      first
      | exact continuous_const
      | exact hf.matrix_elem _ _
  constructor
  · exact block (fun B => B.val) Units.continuous_val
  · have equality : (fun B : BinaryRealGL => ((planeLevi B 1)⁻¹ : RealGL3).val) =
        fun B => planeBlock ((B⁻¹ : BinaryRealGL).val) (1 : ℝ) := by
      funext B
      have := map_inv (planeLeviOneHom (R := ℝ)) B
      change (planeLeviOneHom B)⁻¹.val = (planeLeviOneHom B⁻¹).val
      rw [this]
    rw [equality]
    exact block (fun B => (B⁻¹ : BinaryRealGL).val) Units.continuous_coe_inv

theorem planeLevi_argument_translate (A : BinaryAdelicGL) (g : BinaryRealGL) :
    planeLevi A 1 * 1 * atInfinity (planeLevi g 1) = planeLevi (A * atInfinity g) 1 := by
  rw [mul_one, atInfinity_planeLeviOne]
  exact (planeLeviOneHom.map_mul A (atInfinity g)).symm

/-- The translated source values as a combination of source-cochain cusp vectors. -/
theorem testRealization_sourcePlaneCuspidalValues (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (g : BinaryRealGL) (vertices : Fin 3 → RealGL3) :
    testRealization data.cusp functional g (sourcePlaneCuspidalValues data source cocycle vertices
        1) =
      normPower (GeneralLinearGroup.det (atInfinity g)) (-(((n : ℂ) + 3) / 2)) •
        ∑ m ∈ degreeMonomials n, functional (monomialVector n m) •
          CuspSupNorm.boundedRealization data.cusp
            (cochainCuspVector data source cocycle m vertices (planeLevi g 1)) := by
  rw [lp_ext_iff]
  intro argument
  rw [testRealization_apply, sourcePlaneCuspidalValues_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sum, Finset.sum_apply, smul_eq_mul]
  rw [map_smul, functional_eq_sum_coeff functional, smul_eq_mul, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  change _ = _ * (_ * data.cusp.realize _ argument)
  rw [← coeff_source_translate, planeLevi_argument_translate, map_mul, normPower_mul, mul_one]
  ring

/-- **Source values along continuous vertices are controlled.** -/
theorem sourcePlaneCuspidalValues_controlled (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) {vertices : X → Fin 3 → RealGL3}
    (hvertices : Continuous vertices) :
    Controlled data.cusp (fun x => sourcePlaneCuspidalValues data source cocycle (vertices x) 1) :=
        by
  intro functional
  simp only [testRealization_sourcePlaneCuspidalValues]
  apply (continuous_normPower_det continuous_snd _).smul
  apply continuous_finsetSum
  intro m _
  exact (cochainCuspVector_comp_continuous data source cocycle m _ _
    (hvertices.comp continuous_fst) (continuous_planeLeviOne.comp continuous_snd)).const_smul
    (functional (monomialVector n m))

theorem sourcePlaneGroupCocycle_eq_values (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (first second : RealPlaneGroup) :
    (sourcePlaneGroupCocycle data source cocycle (first, second) :
        cuspidalTensorValues data.cusp (HomogeneousPoly n)) =
      sourcePlaneCuspidalValues data source cocycle
        ![1, realPlaneMatrix first, realPlaneMatrix first * realPlaneMatrix second] 1 := by
  apply Subtype.ext
  funext argument
  rw [sourcePlaneGroupCocycle_apply, sourcePlaneCuspidalValues_apply, mul_one]

theorem continuous_simplex {p q : X → RealPlaneGroup} (hp : PlaneContinuous p)
    (hq : PlaneContinuous q) :
    Continuous (fun x => (![1, realPlaneMatrix (p x), realPlaneMatrix (p x) * realPlaneMatrix (q
        x)] :
      Fin 3 → RealGL3)) :=
  vector3_continuous _ _ _ continuous_const hp.matrix (hp.matrix.mul hq.matrix)

/-- **The plane group cocycle of a source cocycle along continuous paths is controlled.** -/
theorem sourcePlaneGroupCocycle_controlled (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) {p q : X → RealPlaneGroup}
    (hp : PlaneContinuous p) (hq : PlaneContinuous q) :
    Controlled data.cusp (fun x =>
      (sourcePlaneGroupCocycle data source cocycle (p x, q x) :
        cuspidalTensorValues data.cusp (HomogeneousPoly n))) := by
  simp only [sourcePlaneGroupCocycle_eq_values]
  exact sourcePlaneCuspidalValues_controlled data source cocycle (continuous_simplex hp hq)

end TernaryPeriodPolynomials.EdgeControl
