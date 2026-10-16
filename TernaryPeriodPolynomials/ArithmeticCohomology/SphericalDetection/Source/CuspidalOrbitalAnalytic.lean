module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CuspidalAnalyticPullback
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CoefficientRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourcePlaneCuspidalFamily_hilbertContDiffAt {degree : ℕ} {index P : Type} [Fintype index]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) (base : AdelicGL)
    (points : P → Fin 4 → RealGL3) (point : P)
    (regular : ContDiffAt ℝ ⊤ (fun parameter index => (points parameter index).val) point) :
    ContDiffAt ℝ ⊤ (fun parameter =>
      cuspidalTensorHilbertEmbedding data.cusp basis (sourcePlaneCuspidalFamily data source cocycle base (points parameter))) point := by
  have supplied := sourcePlaneCuspidalFamily_hilbertSmooth data basis source cocycle base
  have domain_open : IsOpen {matrices : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ | ∀ index, (matrices index).det ≠ 0} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro index
    exact isOpen_ne_fun ((continuous_apply index).matrix_det) continuous_const
  have inside : (fun index => (points point index).val) ∈
      {matrices : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ | ∀ index, (matrices index).det ≠ 0} :=
    fun index => (points point index).det_ne_zero
  have composed := (supplied.contDiffAt (domain_open.mem_nhds inside)).comp point regular
  convert composed using 1
  funext parameter
  congr 2
  funext index
  exact (invertibleMatrix_coe (points parameter index)).symm

theorem binaryInvertibleMatrix_val_contDiffAt_one :
    ContDiffAt ℝ ⊤ (fun matrix : BinaryRealMatrix => (invertibleMatrix matrix).val) 1 := by
  apply contDiffAt_id.congr_of_eventuallyEq
  have domain_open : IsOpen {matrix : BinaryRealMatrix | matrix.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  filter_upwards [domain_open.mem_nhds (show (1 : BinaryRealMatrix).det ≠ 0 by simp)] with matrix regular
  exact invertibleMatrix_val matrix regular

theorem planeBlockOne_contDiff : ContDiff ℝ ⊤ (fun matrix : BinaryRealMatrix => planeBlock matrix (1 : ℝ)) := by
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  fin_cases row <;> fin_cases column <;> first
    | exact contDiff_const
    | exact (contDiff_apply ℝ ℝ (0 : Fin 2)).comp (contDiff_apply ℝ (Fin 2 → ℝ) (0 : Fin 2))
    | exact (contDiff_apply ℝ ℝ (1 : Fin 2)).comp (contDiff_apply ℝ (Fin 2 → ℝ) (0 : Fin 2))
    | exact (contDiff_apply ℝ ℝ (0 : Fin 2)).comp (contDiff_apply ℝ (Fin 2 → ℝ) (1 : Fin 2))
    | exact (contDiff_apply ℝ ℝ (1 : Fin 2)).comp (contDiff_apply ℝ (Fin 2 → ℝ) (1 : Fin 2))

theorem sourcePlaneCuspidalValues_orbital_analyticAt {degree : ℕ} {index P : Type} [Fintype index]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (vertices : P → Fin 3 → RealGL3) (point : P)
    (regular : ContDiffAt ℝ ⊤ (fun parameter index => (vertices parameter index).val) point) :
    AnalyticAt ℝ (fun parameter : BinaryRealMatrix × P =>
      binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix parameter.1))
        (cuspidalTensorHilbertEmbedding data.cusp basis (sourcePlaneCuspidalValues data source cocycle (vertices parameter.2) 1)))
      (1, point) := by
  let points (parameter : BinaryRealMatrix × P) : Fin 4 → RealGL3 :=
    ![vertices parameter.2 0, vertices parameter.2 1, vertices parameter.2 2,
      planeLevi (invertibleMatrix parameter.1) 1]
  have input_regular : ContDiffAt ℝ ⊤ (fun parameter index => (points parameter index).val) (1, point) := by
    apply contDiffAt_pi.mpr
    intro position
    fin_cases position
    · change ContDiffAt ℝ ⊤ (fun parameter : BinaryRealMatrix × P => (vertices parameter.2 0).val) (1, point)
      exact (contDiffAt_pi.mp regular 0).comp (f := fun parameter : BinaryRealMatrix × P => parameter.2) (1, point) contDiffAt_snd
    · change ContDiffAt ℝ ⊤ (fun parameter : BinaryRealMatrix × P => (vertices parameter.2 1).val) (1, point)
      exact (contDiffAt_pi.mp regular 1).comp (f := fun parameter : BinaryRealMatrix × P => parameter.2) (1, point) contDiffAt_snd
    · change ContDiffAt ℝ ⊤ (fun parameter : BinaryRealMatrix × P => (vertices parameter.2 2).val) (1, point)
      exact (contDiffAt_pi.mp regular 2).comp (f := fun parameter : BinaryRealMatrix × P => parameter.2) (1, point) contDiffAt_snd
    · change ContDiffAt ℝ ⊤ (fun parameter : BinaryRealMatrix × P => planeBlock (invertibleMatrix parameter.1).val (1 : ℝ)) (1, point)
      exact planeBlockOne_contDiff.contDiffAt.comp (1, point)
        (binaryInvertibleMatrix_val_contDiffAt_one.comp (f := fun parameter : BinaryRealMatrix × P => parameter.1) (1, point) contDiffAt_fst)
  have vectors := sourcePlaneCuspidalFamily_hilbertContDiffAt data basis source cocycle 1 points (1, point) input_regular
  have domain_open : IsOpen {matrix : BinaryRealMatrix | matrix.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  have scalar_on := binary_normalizingFactor_contDiffOn (fun matrix : BinaryRealMatrix => matrix)
    (fun row column => by fun_prop) (domain := {matrix : BinaryRealMatrix | matrix.det ≠ 0}) (fun _ member => member)
    (-(((degree : ℂ) + 3) / 2)) (order := ⊤)
  have scalar := (scalar_on.contDiffAt (domain_open.mem_nhds (show (1 : BinaryRealMatrix).det ≠ 0 by simp))).comp
    (1, point) (contDiffAt_fst (E := BinaryRealMatrix) (F := P))
  have combined := (scalar.smul vectors).analyticAt
  convert combined using 1
  funext parameter
  rw [← cuspidalTensorHilbertEmbedding_translation, sourcePlaneCuspidalValues_translation, map_smul]
  congr 2
  have tuple : (fun index : Fin 3 => points parameter index.castSucc) = vertices parameter.2 := by
    funext position
    fin_cases position <;> rfl
  change sourcePlaneCuspidalValues data source cocycle (vertices parameter.2)
      (planeLevi (atInfinity (invertibleMatrix parameter.1)) 1 * 1) =
    sourcePlaneCuspidalValues data source cocycle (fun index => points parameter index.castSucc)
      (1 * atInfinity (points parameter (Fin.last 3)))
  rw [tuple, mul_one, one_mul]
  exact congrArg (sourcePlaneCuspidalValues data source cocycle (vertices parameter.2))
    (atInfinity_planeLeviOne (invertibleMatrix parameter.1)).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
