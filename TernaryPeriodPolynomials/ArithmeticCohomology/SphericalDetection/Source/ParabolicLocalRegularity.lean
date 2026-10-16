module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.ParabolicRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourcePlaneGroupCocycle_hilbertContDiffAt {degree : ℕ} {index P : Type} [Fintype index]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (first second : P → RealPlaneGroup) (center : P)
    (first_regular : ContDiffAt ℝ ⊤ (fun point => (realPlaneMatrix (first point)).val) center)
    (second_regular : ContDiffAt ℝ ⊤ (fun point => (realPlaneMatrix (second point)).val) center) :
    ContDiffAt ℝ ⊤ (fun point => cuspidalTensorHilbertEmbedding data.cusp basis
      (sourcePlaneGroupCocycle data source cocycle (first point, second point))) center := by
  let points (point : P) : Fin 4 → RealGL3 :=
    ![1, realPlaneMatrix (first point), realPlaneMatrix (first point) * realPlaneMatrix (second point), 1]
  have product_regular : ContDiffAt ℝ ⊤
      (fun point => (realPlaneMatrix (first point)).val * (realPlaneMatrix (second point)).val) center := by
    apply contDiffAt_pi.mpr
    intro row
    apply contDiffAt_pi.mpr
    intro column
    change ContDiffAt ℝ ⊤ (fun point => ∑ middle,
      (realPlaneMatrix (first point)).val row middle * (realPlaneMatrix (second point)).val middle column) center
    apply ContDiffAt.sum
    intro middle _
    exact (contDiffAt_pi.mp (contDiffAt_pi.mp first_regular row) middle).mul
      (contDiffAt_pi.mp (contDiffAt_pi.mp second_regular middle) column)
  have input_regular : ContDiffAt ℝ ⊤ (fun point index => (points point index).val) center := by
    apply contDiffAt_pi.mpr
    intro position
    fin_cases position
    · exact contDiffAt_const
    · exact first_regular
    · exact product_regular
    · exact contDiffAt_const
  have composed := sourcePlaneCuspidalFamily_hilbertContDiffAt data basis source cocycle 1 points center input_regular
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

theorem sourcePlaneNormalizedGroupCocycle_hilbertContDiffAt {degree : ℕ} {index P : Type} [Fintype index]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (first second : P → RealPlaneGroup) (center : P)
    (first_regular : ContDiffAt ℝ ⊤ (fun point => (realPlaneMatrix (first point)).val) center)
    (second_regular : ContDiffAt ℝ ⊤ (fun point => (realPlaneMatrix (second point)).val) center) :
    ContDiffAt ℝ ⊤ (fun point => cuspidalTensorHilbertEmbedding data.cusp basis
      (sourcePlaneNormalizedGroupCocycle data source cocycle (first point, second point)).val) center := by
  have regular := sourcePlaneGroupCocycle_hilbertContDiffAt data basis source cocycle first second center first_regular second_regular
  have correction := sourcePlaneGroupCocycle_hilbertContDiffAt data basis source cocycle first (fun _ => 1) center first_regular contDiffAt_const
  convert regular.sub correction using 1
  funext point
  exact sourcePlaneNormalizedGroupCocycle_hilbert data basis source cocycle _ _

end TernaryPeriodPolynomials.SphericalDetection.Helpers
