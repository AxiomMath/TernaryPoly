module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineCoefficientRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourcePlaneCuspidalValues_hilbertContDiff {degree : ℕ} {index P : Type} [Fintype index]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) (base : AdelicGL)
    (vertices : P → Fin 3 → RealGL3)
    (regular : ContDiff ℝ ⊤ (fun point index => (vertices point index).val)) :
    ContDiff ℝ ⊤ (fun point => cuspidalTensorHilbertEmbedding data.cusp basis
      (sourcePlaneCuspidalValues data source cocycle (vertices point) base)) := by
  let points (point : P) : Fin 4 → RealGL3 := ![vertices point 0, vertices point 1, vertices point 2, 1]
  have input_regular : ContDiff ℝ ⊤ (fun point index => (points point index).val) := by
    apply contDiff_pi.mpr
    intro position
    fin_cases position
    · exact contDiff_pi.mp regular 0
    · exact contDiff_pi.mp regular 1
    · exact contDiff_pi.mp regular 2
    · exact contDiff_const
  have composed := sourcePlaneCuspidalFamily_hilbertContDiff data basis source cocycle base points input_regular
  have equality (point : P) : sourcePlaneCuspidalFamily data source cocycle base (points point) =
      sourcePlaneCuspidalValues data source cocycle (vertices point) base := by
    have tuple : (fun index : Fin 3 => points point index.castSucc) = vertices point := by
      funext index
      fin_cases index <;> rfl
    change sourcePlaneCuspidalValues data source cocycle
      (fun index : Fin 3 => points point index.castSucc) (base * atInfinity (1 : RealGL3)) = _
    rw [tuple, atInfinity_one, mul_one]
  simpa only [equality] using composed

theorem sourceCuspidalVertexPrism_hilbertContDiff {degree : ℕ} {index P : Type} [Fintype index]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (projection : RealGL3 → RealGL3) (real : P → RealGL3) (base : AdelicGL)
    (vertices : P → Fin 2 → RealGL3)
    (translated_regular : ContDiff ℝ ⊤ (fun point index => (real point * vertices point index).val))
    (projected_regular : ContDiff ℝ ⊤ (fun point index =>
      (projection (real point * vertices point index)).val))
    (coefficient_regular : ∀ polynomial : HomogeneousPoly degree, ∀ functional : HomogeneousPoly degree →ₗ[ℂ] ℂ,
      ContDiff ℝ ⊤ (fun point => functional (realCoefficientComponent degree data.chi (real point)⁻¹ polynomial))) :
    ContDiff ℝ ⊤ (fun point => cuspidalTensorHilbertEmbedding data.cusp basis
      (sourceCuspidalVertexPrism data source cocycle projection (real point) base (vertices point))) := by
  let first (point : P) : Fin 3 → RealGL3 :=
    ![projection (real point * vertices point 0), real point * vertices point 0, real point * vertices point 1]
  let second (point : P) : Fin 3 → RealGL3 :=
    ![projection (real point * vertices point 0), projection (real point * vertices point 1),
      real point * vertices point 1]
  have first_regular : ContDiff ℝ ⊤ (fun point index => (first point index).val) := by
    apply contDiff_pi.mpr
    intro position
    fin_cases position
    · exact contDiff_pi.mp projected_regular 0
    · exact contDiff_pi.mp translated_regular 0
    · exact contDiff_pi.mp translated_regular 1
  have second_regular : ContDiff ℝ ⊤ (fun point index => (second point index).val) := by
    apply contDiff_pi.mpr
    intro position
    fin_cases position
    · exact contDiff_pi.mp projected_regular 0
    · exact contDiff_pi.mp projected_regular 1
    · exact contDiff_pi.mp translated_regular 1
  have prism_regular := (sourcePlaneCuspidalValues_hilbertContDiff data basis source cocycle base first
    first_regular).sub (sourcePlaneCuspidalValues_hilbertContDiff data basis source cocycle base second second_regular)
  simp only [sourceCuspidalVertexPrism, cuspidalTensorHilbertEmbedding_map]
  apply contDiff_pi.mpr
  intro position
  simp only [basisHilbertCoefficient_apply]
  apply ContDiff.sum
  intro source_index _
  apply (coefficient_regular (basis source_index) (basis.coord position)).smul
  simpa only [homogeneousVertexPrism, map_sub, Pi.sub_apply, first, second] using
    contDiff_pi.mp prism_regular source_index

end TernaryPeriodPolynomials.SphericalDetection.Helpers
