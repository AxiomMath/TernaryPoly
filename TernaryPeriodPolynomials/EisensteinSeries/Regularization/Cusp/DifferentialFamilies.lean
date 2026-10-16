module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.DifferentialWords

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cusp_family_productOrbit_contDiffOn
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (cusp : CuspidalRepresentation) (family : X → cusp.smooth) {domain : Set X}
    (smooth : ContDiffOn ℝ ⊤
      (fun input : X × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        cusp.π (atInfinity (invertibleMatrix (input.2 0))) (family input.1).val)
      (domain ×ˢ {entries | ∀ index, (entries index).det ≠ 0})) :
    ContDiffOn ℝ ⊤
      (fun input : (X × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)) ×
          (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        cusp.π (atInfinity (invertibleMatrix (input.1.2 0)))
          (cusp.π (atInfinity (invertibleMatrix (input.2 0))) (family input.1.1).val))
      ((domain ×ˢ {entries | ∀ index, (entries index).det ≠ 0}) ×ˢ
        {entries | ∀ index, (entries index).det ≠ 0}) := by
  let productEntries (input : (X × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)) ×
      (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)) : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ :=
    fun _ => input.1.2 0 * input.2 0
  have product_smooth : ContDiff ℝ ⊤ productEntries := by
    apply contDiff_pi.mpr
    intro index
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    simp only [productEntries, Matrix.mul_apply, Fin.sum_univ_two]
    fun_prop
  have product_value (input)
      (member : input ∈ ((domain ×ˢ
          {entries : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ | ∀ index, (entries index).det ≠ 0}) ×ˢ
        {entries | ∀ index, (entries index).det ≠ 0})) :
      productEntries input 0 =
        (invertibleMatrix (input.1.2 0) * invertibleMatrix (input.2 0)).val := by
    simp only [productEntries, Units.val_mul, invertibleMatrix, dite_eq_left (member.1.2 0),
      dite_eq_left (member.2 0), GeneralLinearGroup.val_mkOfDetNeZero]
  have maps : Set.MapsTo (fun input => (input.1.1, productEntries input))
      ((domain ×ˢ {entries | ∀ index, (entries index).det ≠ 0}) ×ˢ
        {entries | ∀ index, (entries index).det ≠ 0})
      (domain ×ˢ {entries | ∀ index, (entries index).det ≠ 0}) := by
    intro input member
    refine ⟨member.1.1, ?_⟩
    intro index
    change (productEntries input 0).det ≠ 0
    rw [product_value input member]
    exact (invertibleMatrix (input.1.2 0) * invertibleMatrix (input.2 0)).det_ne_zero
  apply (smooth.comp ((contDiff_fst.fst).prodMk product_smooth).contDiffOn maps).congr
  intro input member
  change cusp.π _ (cusp.π _ (family input.1.1).val) =
    cusp.π (atInfinity (invertibleMatrix (productEntries input 0))) (family input.1.1).val
  rw [product_value input member, invertibleMatrix_val, binary_atInfinity_mul,
    map_mul, Module.End.mul_apply]

theorem cusp_family_infinitesimalOrbit_contDiffOn
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (cusp : CuspidalRepresentation) (family : X → cusp.smooth) {domain : Set X}
    (domain_open : IsOpen domain)
    (smooth : ContDiffOn ℝ ⊤
      (fun input : X × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        cusp.π (atInfinity (invertibleMatrix (input.2 0))) (family input.1).val)
      (domain ×ˢ {entries | ∀ index, (entries index).det ≠ 0}))
    (direction : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiffOn ℝ ⊤
      (fun input : X × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        cusp.π (atInfinity (invertibleMatrix (input.2 0)))
          (cuspSmoothInfinitesimalAction cusp direction (family input.1)).val)
      (domain ×ˢ {entries | ∀ index, (entries index).det ≠ 0}) := by
  intro input member
  have product_smooth := (cusp_family_productOrbit_contDiffOn cusp family smooth).contDiffAt
    (((domain_open.prod (invertibleMatrixTuples_isOpen 2 1)).prod
      (invertibleMatrixTuples_isOpen 2 1)).mem_nhds
      (show (input, fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∈
          ((domain ×ˢ {entries | ∀ index, (entries index).det ≠ 0}) ×ˢ
            {entries | ∀ index, (entries index).det ≠ 0}) from
        ⟨member, fun _ => by simp⟩))
  have derivative_smooth : ContDiffAt ℝ ⊤
      (fun first : X × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        fderiv ℝ (fun second : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
          cusp.π (atInfinity (invertibleMatrix (first.2 0)))
            (cusp.π (atInfinity (invertibleMatrix (second 0))) (family first.1).val)) (fun _ => 1))
      input := by
    apply ContDiffAt.fderiv (n := ⊤)
      (f := fun (first : X × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ))
          (second : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        cusp.π (atInfinity (invertibleMatrix (first.2 0)))
          (cusp.π (atInfinity (invertibleMatrix (second 0))) (family first.1).val))
      (g := fun _ => fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ))
    · exact product_smooth
    · exact contDiffAt_const
    · exact le_top
  have evaluated := derivative_smooth.clm_apply (contDiffAt_const (c := direction))
  apply (evaluated.congr_of_eventuallyEq ?_).contDiffWithinAt
  exact Filter.Eventually.of_forall (fun nearby =>
    (cuspInfinitesimalAction_left_translate_fderiv cusp direction (family nearby.1)
      (invertibleMatrix (nearby.2 0))).symm)

theorem cusp_family_differentialWordOrbit_contDiffOn
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (cusp : CuspidalRepresentation) (family : X → cusp.smooth) {domain : Set X}
    (domain_open : IsOpen domain)
    (smooth : ContDiffOn ℝ ⊤
      (fun input : X × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        cusp.π (atInfinity (invertibleMatrix (input.2 0))) (family input.1).val)
      (domain ×ˢ {entries | ∀ index, (entries index).det ≠ 0}))
    (directions : List (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)) :
    ContDiffOn ℝ ⊤
      (fun input : X × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        cusp.π (atInfinity (invertibleMatrix (input.2 0)))
          (cuspDifferentialWord cusp directions (family input.1)).val)
      (domain ×ˢ {entries | ∀ index, (entries index).det ≠ 0}) := by
  induction directions with
  | nil => exact smooth
  | cons direction directions induction =>
    exact cusp_family_infinitesimalOrbit_contDiffOn cusp
      (fun point => cuspDifferentialWord cusp directions (family point)) domain_open induction direction

theorem cusp_family_differentialWord_contDiffOn
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (cusp : CuspidalRepresentation) (family : X → cusp.smooth) {domain : Set X}
    (domain_open : IsOpen domain)
    (smooth : ContDiffOn ℝ ⊤
      (fun input : X × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        cusp.π (atInfinity (invertibleMatrix (input.2 0))) (family input.1).val)
      (domain ×ˢ {entries | ∀ index, (entries index).det ≠ 0}))
    (directions : List (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)) :
    ContDiffOn ℝ ⊤ (fun point => (cuspDifferentialWord cusp directions (family point)).val) domain := by
  have orbit_smooth := cusp_family_differentialWordOrbit_contDiffOn cusp family domain_open smooth directions
  have at_identity := orbit_smooth.comp
    (contDiffOn_id.prodMk (contDiffOn_const (c := fun _ : Fin 1 =>
      (1 : Matrix (Fin 2) (Fin 2) ℝ))))
    (fun _ member => ⟨member, fun _ => by simp⟩)
  have matrix_one : invertibleMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    simpa only [Units.val_one] using invertibleMatrix_val (1 : BinaryRealGL)
  simpa only [Function.comp_def, id_eq, matrix_one, binary_atInfinity_one, map_one,
    Module.End.one_apply] using at_identity

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
