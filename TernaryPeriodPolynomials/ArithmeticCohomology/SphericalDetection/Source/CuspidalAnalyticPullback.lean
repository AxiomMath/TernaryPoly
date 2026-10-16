module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperRadicalBinary
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorSmoothCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourcePlaneCuspidalFamily_hilbertContDiff {degree : ℕ} {index P : Type} [Fintype index]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) (base : AdelicGL)
    (points : P → Fin 4 → RealGL3)
    (regular : ContDiff ℝ ⊤ (fun parameter index => (points parameter index).val)) :
    ContDiff ℝ ⊤ (fun parameter =>
      cuspidalTensorHilbertEmbedding data.cusp basis (sourcePlaneCuspidalFamily data source cocycle base (points parameter))) := by
  have supplied := sourcePlaneCuspidalFamily_hilbertSmooth data basis source cocycle base
  have maps (parameter : P) (_ : parameter ∈ Set.univ) :
      (fun index => (points parameter index).val) ∈ {matrices : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ | ∀ index, (matrices index).det ≠ 0} := by
    intro index
    exact (points parameter index).det_ne_zero
  have composed := supplied.comp regular.contDiffOn maps
  rw [contDiffOn_univ] at composed
  convert composed using 1
  funext parameter
  congr 2
  funext index
  exact (invertibleMatrix_coe (points parameter index)).symm

theorem sourcePlaneCuspidalValues_translation {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (vertices : Fin 3 → RealGL3) (base : AdelicGL) (element : BinaryAdelicGL) :
    cuspidalTensorTranslation data.cusp element (sourcePlaneCuspidalValues data source cocycle vertices base) =
      normPower (GeneralLinearGroup.det element) (-(((degree : ℂ) + 3) / 2)) •
        sourcePlaneCuspidalValues data source cocycle vertices (planeLevi element 1 * base) := by
  apply Subtype.ext
  funext argument
  change (sourcePlaneCuspidalValues data source cocycle vertices base).val (argument * element) = _
  rw [sourcePlaneCuspidalValues_apply]
  change normPower (GeneralLinearGroup.det (argument * element)) (-(((degree : ℂ) + 3) / 2)) •
      source vertices (planeLevi (argument * element) 1 * base) =
    normPower (GeneralLinearGroup.det element) (-(((degree : ℂ) + 3) / 2)) •
      (sourcePlaneCuspidalValues data source cocycle vertices (planeLevi element 1 * base)).val argument
  rw [sourcePlaneCuspidalValues_apply, map_mul, normPower_mul, ← smul_smul]
  have levi : planeLevi (argument * element) 1 = planeLevi argument 1 * planeLevi element 1 :=
    planeLeviOneHom.map_mul argument element
  rw [levi, mul_assoc, smul_comm]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
