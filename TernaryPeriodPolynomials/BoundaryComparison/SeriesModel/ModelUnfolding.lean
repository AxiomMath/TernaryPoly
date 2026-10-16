module

public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.CochainReduction

@[expose] public section


/-!
# Unfolding the model Eisenstein cocycle: a sum over rational plane flags

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeriesModel

open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein

theorem sectionEisensteinValue_apply {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (sec : StandardConstruction.SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) :
    (ConvergentEisenstein.SectionSpace.sectionEisensteinValue data holomorphic sec).val argument =
      ∑' flag : Flags .plane, sec.val (rationalGroup flag.out⁻¹ * argument) := by
  change EisensteinValue.eisensteinValue data holomorphic (ConvergentEisenstein.SectionSpace.linearFlatExtension data holomorphic sec) argument = _
  rw [EisensteinValue.eisensteinValue_apply]
  refine tsum_congr fun flag => ?_
  change (ConvergentEisenstein.SectionSpace.linearFlatExtension data holomorphic sec).val cohomologicalPoint
      (rationalGroup flag.out⁻¹ * argument) = _
  rw [ConvergentEisenstein.SectionSpace.linearFlatExtension_endpoint data holomorphic sec]

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FlatExtensions in
/-- **The model Eisenstein cocycle, coefficient by coefficient, is the sum over rational plane flags of the source cocycle**:
for a monomial `m` of degree `n`,
`coeff_m 𝓔(D,c)(vertices) = ∑'_{flag ∈ P(ℚ)\G(ℚ)} coeff_m c(realVertices)( γ_flag⁻¹ · (vertices₀)⁻¹ )`. -/
theorem globalCocycle_coeff {n : ℕ} (D : InducingData n) (hol : PlaneEisensteinConvergent D) (hn : 4 ≤ n)
    (c : SourceSpace.sourceCocycles D .plane) (vertices : Fin 3 → RationalGL3) (m : Fin 3 →₀ ℕ)
    (hm : Finsupp.degree m = n) :
    ((EndpointEisensteinCocycle.globalCocycle D hol hn c).val.val vertices).val.coeff m =
      ∑' flag : Flags .plane, ((c.val (GlobalEisensteinCocycle.realVertices vertices))
          (rationalGroup flag.out⁻¹ * rationalGroup ((vertices 0)⁻¹))).val.coeff m := by
  change (PolynomialEisenstein.polynomialValue D hol
    (PolynomialEisenstein.sourceSection D c (GlobalEisensteinCocycle.realVertices vertices))
    (rationalGroup ((vertices 0)⁻¹))).val.coeff m = _
  change (FlatExtensions.assemblePolynomial n _).val.coeff m = _
  rw [assemblePolynomial_coeff, ite_eq_left hm]
  exact sectionEisensteinValue_apply D hol _ _

end TernaryPeriodPolynomials.Argument.FormSeriesModel
