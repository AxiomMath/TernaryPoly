module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.RightEquivariance

@[expose] public section


/-!
# `DiagonalDatum` from a factorization `λ̃ · R`

The two-variable family of `RightEquivariance.DiagonalDatum` is built from the canonical objects of
steps 3-5 of the edge-convergence plan. For a family `Φ z` of plane sections with
`Φ 0 = R(h) f`, suppose that near `s₀` (with `s ≠ s₀`) the chosen standard continuation of the flat
family of `Φ z`, evaluated at `g`, is `λ̃(s) · R(s, z)`, where

* `λ̃` is holomorphic on the punctured closed disc `0 < |s - s₀| ≤ r` (no pole there),
* `R(·, z)` is holomorphic on the closed disc and `R` is jointly continuous (the local standard
  integral, holomorphic in the parameter and jointly continuous in the section parameter `z`),

and likewise for `f` at `g h` with `R_f`, where `R_f(s) = R(s, s - s₀)` (the integrand identity
`SectionMultipliersFlat.flat_twist_diagonal`). Then the family
`G(s, z) = λ̃(s) R(s, z)` for `s ≠ s₀`, `G(s₀, z) = cont(Φ z)(s₀)(g)` is a `DiagonalDatum`: for each
fixed `z` it is holomorphic across `s₀` because the chosen continuation is analytic at `s₀`
(Sol's `HasRegularStandard`), whatever the pole order of `λ̃` at `s₀`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Metric Filter Topology
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.RightEquivariance

open scoped Classical in
/-- The glued family: `λ̃ R` off `s₀` and the (analytic) endpoint value of the chosen continuation
at `s₀`. -/
def factorizedFamily {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sections : ℂ → SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) (scalar : ℂ → ℂ) (local_ : ℂ → ℂ → ℂ) : ℂ → ℂ → ℂ :=
  fun parameter z => if parameter = cohomologicalPoint then
    sectionContinuation data holomorphic (sections z) cohomologicalPoint argument
    else scalar parameter * local_ parameter z

/-- A `DiagonalDatum` from the factorization `λ̃ · R`. -/
def diagonalDatum_of_factorization {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (real : RealGL3) (argument : AdelicGL)
    (sections : ℂ → SectionSpace.inducedSections data .plane cohomologicalPoint)
    (sections_zero : sections 0 =
      RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue)
    (scalar : ℂ → ℂ) (local_ : ℂ → ℂ → ℂ) (localTranslate : ℂ → ℂ) (radius width : ℝ)
    (radius_pos : 0 < radius) (width_pos : 0 < width)
    (scalar_diff : DifferentiableOn ℂ scalar (closedBall cohomologicalPoint radius \ {cohomologicalPoint}))
    (local_diff : ∀ z : ℂ, ‖z‖ < width →
      DifferentiableOn ℂ (fun parameter => local_ parameter z) (closedBall cohomologicalPoint radius))
    (local_continuous : ContinuousOn (fun p : ℂ × ℂ => local_ p.1 p.2)
      (closedBall cohomologicalPoint radius ×ˢ ball (0 : ℂ) width))
    (factor : ∀ z : ℂ, ‖z‖ < width → ∀ᶠ parameter in 𝓝[≠] cohomologicalPoint,
      sectionContinuation data holomorphic (sections z) parameter argument =
        scalar parameter * local_ parameter z)
    (factor_translate : ∀ᶠ parameter in 𝓝[≠] cohomologicalPoint,
      sectionContinuation data holomorphic sectionValue parameter (argument * atInfinity real) =
        scalar parameter * localTranslate parameter)
    (translate_eq : ∀ parameter : ℂ, parameter ≠ cohomologicalPoint →
      dist parameter cohomologicalPoint < radius →
      localTranslate parameter = local_ parameter (parameter - cohomologicalPoint)) :
    DiagonalDatum data holomorphic sectionValue real argument where
  family := factorizedFamily data holomorphic sections argument scalar local_
  radius := radius
  width := width
  radius_pos := radius_pos
  width_pos := width_pos
  axis := by
    simp [factorizedFamily, sections_zero]
  diagonal := by
    filter_upwards [factor_translate, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ radius_pos),
      self_mem_nhdsWithin] with parameter translated inside different
    have notPoint : parameter ≠ cohomologicalPoint := different
    simp only [factorizedFamily, ite_eq_right notPoint]
    rw [translated, translate_eq parameter notPoint inside]
  holomorphic_in_parameter := by
    intro z hz parameter membership
    by_cases atPoint : parameter = cohomologicalPoint
    · subst atPoint
      have germ := eventually_nhdsWithin_iff.mp (factor z hz)
      have agree : (fun s => factorizedFamily data holomorphic sections argument scalar local_ s z)
          =ᶠ[𝓝 cohomologicalPoint]
          (fun s => sectionContinuation data holomorphic (sections z) s argument) := by
        filter_upwards [germ] with s hs
        by_cases same : s = cohomologicalPoint
        · subst same
          simp [factorizedFamily]
        · simp only [factorizedFamily, ite_eq_right same]
          exact (hs same).symm
      exact ((sectionContinuation_analyticAt data holomorphic (sections z) argument
        ).differentiableAt.congr_of_eventuallyEq agree).differentiableWithinAt
    · have nearby : {cohomologicalPoint}ᶜ ∈ 𝓝 parameter :=
        isOpen_compl_singleton.mem_nhds atPoint
      have agree : (fun s => factorizedFamily data holomorphic sections argument scalar local_ s z)
          =ᶠ[𝓝 parameter] (fun s => scalar s * local_ s z) := by
        filter_upwards [nearby] with s hs
        have notPoint : s ≠ cohomologicalPoint := hs
        simp only [factorizedFamily, ite_eq_right notPoint]
      have neighbourhood : closedBall cohomologicalPoint radius \ {cohomologicalPoint} ∈
          𝓝[closedBall cohomologicalPoint radius] parameter := by
        rw [Set.sdiff_eq]
        exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds nearby)
      have scalarAt : DifferentiableWithinAt ℂ scalar (closedBall cohomologicalPoint radius)
          parameter :=
        (scalar_diff parameter ⟨membership, atPoint⟩).mono_of_mem_nhdsWithin neighbourhood
      refine (scalarAt.mul (local_diff z hz parameter membership)).congr_of_eventuallyEq
        (agree.filter_mono nhdsWithin_le_nhds) ?_
      simp only [factorizedFamily, ite_eq_right atPoint]
      rfl
  continuous_on_circle := by
    have onSphere : ∀ p ∈ sphere cohomologicalPoint radius ×ˢ ball (0 : ℂ) width,
        factorizedFamily data holomorphic sections argument scalar local_ p.1 p.2 =
          scalar p.1 * local_ p.1 p.2 := by
      intro p membership
      have notPoint : p.1 ≠ cohomologicalPoint := by
        intro equal
        have onCircle := mem_sphere.mp membership.1
        rw [equal, dist_self] at onCircle
        exact radius_pos.ne onCircle
      simp only [factorizedFamily, ite_eq_right notPoint]
    have scalarContinuous : ContinuousOn scalar (sphere cohomologicalPoint radius) := by
      refine scalar_diff.continuousOn.mono ?_
      intro s membership
      refine ⟨sphere_subset_closedBall membership, ?_⟩
      intro equal
      have onCircle := mem_sphere.mp membership
      rw [Set.mem_singleton_iff.mp equal, dist_self] at onCircle
      exact radius_pos.ne onCircle
    refine ContinuousOn.congr ?_ onSphere
    exact (scalarContinuous.comp continuousOn_fst (fun p membership => membership.1)).mul
      (local_continuous.mono (Set.prod_mono sphere_subset_closedBall subset_rfl))

end TernaryPeriodPolynomials.EdgeConvergence.RightEquivariance
