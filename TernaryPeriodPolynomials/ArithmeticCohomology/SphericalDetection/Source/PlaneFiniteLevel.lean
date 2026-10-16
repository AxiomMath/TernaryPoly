module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneCuspidalAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IntegralAdelicNorm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspidalTensorFiniteLevel (cusp : CuspidalRepresentation) (V : Type) [AddCommGroup V] [Module ℂ V] :
    Submodule ℂ (cuspidalTensorValues cusp V) where
  carrier := {values | ∀ matrix : GeneralLinearGroup (Fin 2) IntegralAdeles, ∀ argument,
    values.val (argument * atFinite (GeneralLinearGroup.map integralEmbedding matrix)) = values.val argument}
  zero_mem' := by
    intro matrix argument
    rfl
  add_mem' {first second} first_fixed second_fixed := by
    intro matrix argument
    change first.val _ + second.val _ = first.val _ + second.val _
    rw [first_fixed, second_fixed]
  smul_mem' scalar values fixed := by
    intro matrix argument
    change scalar • values.val _ = scalar • values.val _
    rw [fixed]

theorem planeLevi_finiteLevel (matrix : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    planeLevi (GeneralLinearGroup.map integralEmbedding matrix) 1 ∈ finiteLevel := by
  refine ⟨planeLevi matrix 1, ?_, map_planeLevi_one integralEmbedding matrix⟩
  change lastRow ᵥ* (GeneralLinearGroup.map integralReduction (planeLevi matrix 1)).val = lastRow
  funext column
  fin_cases column <;>
    simp [lastRow, Matrix.vecMul, dotProduct, Fin.sum_univ_three, GeneralLinearGroup.map_apply, planeLevi, planeBlock]

theorem atFinite_planeLeviOne (matrix : BinaryFiniteGL) :
    atFinite (planeLevi matrix 1) = planeLevi (atFinite matrix) 1 := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [atFinite, combineGL, pairMatrix, planeLevi, planeBlock]

theorem source_finiteLevel {degree : ℕ} (data : InducingData degree) (side : Side) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data side source) (vertices : Fin 3 → RealGL3)
    (element : finiteLevel) (base : AdelicGL) :
    source vertices (base * atFinite element.val) = source vertices base := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact (cocycle.1 vertices monomial).2.1 element base

theorem sourcePlaneCuspidalValues_finiteLevel {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (vertices : Fin 3 → RealGL3) (base : RealGL3) :
    sourcePlaneCuspidalValues data source cocycle vertices (atInfinity base) ∈
      cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly degree) := by
  intro matrix argument
  rw [sourcePlaneCuspidalValues_apply, sourcePlaneCuspidalValues_apply, map_mul, normPower_mul,
    normPower_binaryFiniteIntegral, mul_one]
  have levi_mul (first second : BinaryAdelicGL) : planeLevi (first * second) 1 = planeLevi first 1 * planeLevi second 1 :=
    planeLeviOneHom.map_mul first second
  rw [levi_mul, ← atFinite_planeLeviOne]
  rw [mul_assoc]
  rw [← (atInfinity_commute_atFinite base (planeLevi (GeneralLinearGroup.map integralEmbedding matrix) 1)).eq,
    ← mul_assoc]
  rw [source_finiteLevel data .plane source cocycle vertices
    ⟨_, planeLevi_finiteLevel matrix⟩]

theorem realPlaneCuspidalRep_finiteLevel (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (element : RealPlaneGroup) (values : cuspidalTensorValues cusp (HomogeneousPoly degree))
    (fixed : values ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)) :
    (realPlaneCuspidalRep degree cusp character).ρ element values ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) := by
  intro matrix argument
  rw [realPlaneCuspidalRep_apply, realPlaneCuspidalRep_apply, mul_assoc,
    ← (atInfinity_commute_atFinite element.right (GeneralLinearGroup.map integralEmbedding matrix)).eq,
    ← mul_assoc, fixed]

def realPlaneLevelCuspidalRep (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter) :
    Rep ℂ RealPlaneGroup := by
  letI : AddCommGroup (cuspidalTensorValues cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues cusp (HomogeneousPoly degree)).addCommGroup
  letI : AddCommGroup (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)).addCommGroup
  letI : Module ℂ (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)).module
  exact Rep.of (X := cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    ((realPlaneCuspidalRep degree cusp character).ρ.subrepresentation
      (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
      (fun element values fixed => realPlaneCuspidalRep_finiteLevel degree cusp character element values fixed))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
