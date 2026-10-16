module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.DifferentialFamilies

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cusp_family_parameter_contDiffOn
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (cusp : CuspidalRepresentation) (family : X → cusp.smooth) {domain : Set X}
    (smooth : ContDiffOn ℝ ⊤
      (fun input : X × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        cusp.π (atInfinity (invertibleMatrix (input.2 0))) (family input.1).val)
      (domain ×ˢ {entries | ∀ index, (entries index).det ≠ 0})) :
    ContDiffOn ℝ ⊤ (fun point => (family point).val) domain := by
  have restricted := smooth.comp
    (contDiffOn_id.prodMk (contDiffOn_const (c := fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℝ))))
    (fun _ member => ⟨member, fun _ => by simp⟩)
  have matrix_one : invertibleMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    simpa only [Units.val_one] using invertibleMatrix_val (1 : BinaryRealGL)
  simpa only [Function.comp_def, id_eq, matrix_one, binary_atInfinity_one, map_one, Module.End.one_apply]
    using restricted

theorem cusp_family_parameter_translate_fderiv
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (cusp : CuspidalRepresentation) (family : X → cusp.smooth) {point : X}
    (differentiable : DifferentiableAt ℝ (fun point => (family point).val) point)
    (matrix : BinaryAdelicGL) (direction : X) :
    fderiv ℝ (fun nearby => cusp.π matrix (family nearby).val) point direction =
      cusp.π matrix (fderiv ℝ (fun nearby => (family nearby).val) point direction) := by
  have derivative := (cuspRealUnitaryAction cusp matrix).toContinuousLinearMap.hasFDerivAt.comp
    point differentiable.hasFDerivAt
  exact congrArg (fun linear => linear direction) derivative.fderiv

theorem cusp_family_parameter_fderiv_orbit_smooth
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (cusp : CuspidalRepresentation) (family : X → cusp.smooth) {domain : Set X}
    (domain_open : IsOpen domain)
    (smooth : ContDiffOn ℝ ⊤
      (fun input : X × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        cusp.π (atInfinity (invertibleMatrix (input.2 0))) (family input.1).val)
      (domain ×ˢ {entries | ∀ index, (entries index).det ≠ 0}))
    {point : X} (member : point ∈ domain) (direction : X) :
    Smooth (fun realElements : Fin 1 → BinaryRealGL =>
      cusp.π (atInfinity (realElements 0))
        (fderiv ℝ (fun nearby => (family nearby).val) point direction)) := by
  have differentiable := ((cusp_family_parameter_contDiffOn cusp family smooth).contDiffAt
    (domain_open.mem_nhds member)).differentiableAt (by simp)
  intro entries entries_member
  have joint := smooth.contDiffAt
    ((domain_open.prod (invertibleMatrixTuples_isOpen 2 1)).mem_nhds
      (show (point, entries) ∈ domain ×ˢ {entries | ∀ index, (entries index).det ≠ 0} from
        ⟨member, entries_member⟩))
  have swapped : ContDiffAt ℝ ⊤
      (fun input : (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) × X =>
        cusp.π (atInfinity (invertibleMatrix (input.1 0))) (family input.2).val) (entries, point) := by
    exact joint.comp (entries, point) (contDiffAt_snd.prodMk contDiffAt_fst)
  have derivative_smooth : ContDiffAt ℝ ⊤
      (fun first : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
        fderiv ℝ (fun second : X =>
          cusp.π (atInfinity (invertibleMatrix (first 0))) (family second).val) point) entries := by
    apply ContDiffAt.fderiv (n := ⊤)
      (f := fun (first : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) (second : X) =>
        cusp.π (atInfinity (invertibleMatrix (first 0))) (family second).val)
      (g := fun _ => point)
    · exact swapped
    · exact contDiffAt_const
    · exact le_top
  have evaluated := derivative_smooth.clm_apply (contDiffAt_const (c := direction))
  apply (evaluated.congr_of_eventuallyEq ?_).contDiffWithinAt
  exact Filter.Eventually.of_forall (fun nearby =>
    (cusp_family_parameter_translate_fderiv cusp family differentiable
      (atInfinity (invertibleMatrix (nearby 0))) direction).symm)

theorem cusp_family_parameter_fderiv_mem_smooth
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (cusp : CuspidalRepresentation) (family : X → cusp.smooth) {domain : Set X}
    (domain_open : IsOpen domain)
    (smooth : ContDiffOn ℝ ⊤
      (fun input : X × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        cusp.π (atInfinity (invertibleMatrix (input.2 0))) (family input.1).val)
      (domain ×ˢ {entries | ∀ index, (entries index).det ≠ 0}))
    (level : Subgroup BinaryFiniteGL) (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (fixed : ∀ finite : level, ∀ nearby, cusp.π (atFinite finite.val) (family nearby).val = (family nearby).val)
    {point : X} (member : point ∈ domain) (direction : X) :
    fderiv ℝ (fun nearby => (family nearby).val) point direction ∈ cusp.smooth := by
  apply (cusp.smooth_exact _).mpr
  refine ⟨cusp_family_parameter_fderiv_orbit_smooth cusp family domain_open smooth member direction,
    level, level_open, level_compact, ?_⟩
  have differentiable := ((cusp_family_parameter_contDiffOn cusp family smooth).contDiffAt
    (domain_open.mem_nhds member)).differentiableAt (by simp)
  intro finite
  rw [← cusp_family_parameter_translate_fderiv cusp family differentiable]
  congr 2
  funext nearby
  exact fixed finite nearby

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
