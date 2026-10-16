module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.NormalizedRadical

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourcePlaneGroupCocycle_hilbertContDiff {degree : ℕ} {index P : Type} [Fintype index]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (first second : P → RealPlaneGroup)
    (first_regular : ContDiff ℝ ⊤ (fun point => (realPlaneMatrix (first point)).val))
    (second_regular : ContDiff ℝ ⊤ (fun point => (realPlaneMatrix (second point)).val)) :
    ContDiff ℝ ⊤ (fun point => cuspidalTensorHilbertEmbedding data.cusp basis
      (sourcePlaneGroupCocycle data source cocycle (first point, second point))) := by
  let points (point : P) : Fin 4 → RealGL3 :=
    ![1, realPlaneMatrix (first point), realPlaneMatrix (first point) * realPlaneMatrix (second point), 1]
  have product_regular : ContDiff ℝ ⊤
      (fun point => (realPlaneMatrix (first point)).val * (realPlaneMatrix (second point)).val) := by
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    change ContDiff ℝ ⊤ (fun point => ∑ middle,
      (realPlaneMatrix (first point)).val row middle * (realPlaneMatrix (second point)).val middle column)
    apply ContDiff.sum
    intro middle _
    exact ((contDiff_pi.mp (contDiff_pi.mp first_regular row) middle).mul
      (contDiff_pi.mp (contDiff_pi.mp second_regular middle) column))
  have input_regular : ContDiff ℝ ⊤ (fun point index => (points point index).val) := by
    apply contDiff_pi.mpr
    intro position
    fin_cases position
    · exact contDiff_const
    · exact first_regular
    · exact product_regular
    · exact contDiff_const
  have composed := sourcePlaneCuspidalFamily_hilbertContDiff data basis source cocycle 1 points input_regular
  convert composed using 1
  funext point
  apply congrArg (cuspidalTensorHilbertEmbedding data.cusp basis)
  apply Subtype.ext
  funext argument
  rw [sourcePlaneGroupCocycle_apply]
  change _ = normPower (GeneralLinearGroup.det argument) (-(((degree : ℂ) + 3) / 2)) •
    source (fun index => points point index.castSucc) (planeLevi argument 1 * (1 * atInfinity (1 : RealGL3)))
  rw [atInfinity_one, mul_one, mul_one]
  have tuple : (fun index : Fin 3 => points point index.castSucc) =
      ![1, realPlaneMatrix (first point), realPlaneMatrix (first point) * realPlaneMatrix (second point)] := by
    funext position
    fin_cases position <;> rfl
  rw [tuple]

theorem sourcePlaneNormalizedGroupCocycle_hilbertContDiff {degree : ℕ} {index P : Type} [Fintype index]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (first second : P → RealPlaneGroup)
    (first_regular : ContDiff ℝ ⊤ (fun point => (realPlaneMatrix (first point)).val))
    (second_regular : ContDiff ℝ ⊤ (fun point => (realPlaneMatrix (second point)).val)) :
    ContDiff ℝ ⊤ (fun point => cuspidalTensorHilbertEmbedding data.cusp basis
      (sourcePlaneNormalizedGroupCocycle data source cocycle (first point, second point)).val) := by
  have regular := sourcePlaneGroupCocycle_hilbertContDiff data basis source cocycle first second first_regular second_regular
  have correction := sourcePlaneGroupCocycle_hilbertContDiff data basis source cocycle first (fun _ => 1) first_regular contDiff_const
  convert regular.sub correction using 1
  funext point
  exact sourcePlaneNormalizedGroupCocycle_hilbert data basis source cocycle _ _

end TernaryPeriodPolynomials.SphericalDetection.Helpers
