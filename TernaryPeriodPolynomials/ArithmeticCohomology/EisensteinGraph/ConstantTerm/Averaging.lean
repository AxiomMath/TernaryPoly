module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Interface
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Basic

@[expose] public section



open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section
namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

/-! ## Grid averaging (the part used downstream) -/

section GridAverage

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem gridAverage_sub (Θ Θ' : ℝ × ℝ → (Fin 3 → RationalGL3) → V) (K : ℕ) :
    gridAverage (fun r x => Θ r x - Θ' r x) K = gridAverage Θ K - gridAverage Θ' K := by
  funext x
  simp [gridAverage, Finset.sum_sub_distrib, smul_sub]

theorem gridAverage_const (ω : (Fin 3 → RationalGL3) → V) {K : ℕ} (hK : K ≠ 0) :
    gridAverage (fun _ => ω) K = ω := by
  funext x
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  simp only [gridAverage, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
  have : 1 / (K : ℂ) ^ 2 * (K : ℂ) * (K : ℂ) = 1 := by field_simp
  rw [this, one_smul]

end GridAverage

/-! ## Defect decomposition -/

section Defect

variable {n : ℕ} (large : 4 ≤ n) (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
  (c : SourceSpace.sourceCocycles D .plane)

theorem sideUnipotent_add (side : Side) {R : Type*} [CommRing R] (s t s' t' : R) :
    sideUnipotent side (s + s') (t + t') = sideUnipotent side s t * sideUnipotent side s' t' := by
  cases side
  · exact planeUnipotent_add _ _ _ _
  · exact lineUnipotent_add _ _ _ _

theorem sideUnipotent_zero (side : Side) {R : Type*} [CommRing R] :
    sideUnipotent side (0 : R) 0 = 1 := by
  cases side
  · exact (planeUnipotentHom R).map_one
  · exact (lineUnipotentHom R).map_one

theorem defectValue_plane (y : Fin 3 → RealGL3) (g : AdelicGL) :
    defectValue large D hol c .plane y g = eisensteinValue D hol c y g - c.val y g := rfl

theorem defectValue_line (y : Fin 3 → RealGL3) (g : AdelicGL) :
    defectValue large D hol c .line y g = eisensteinValue D hol c y g -
      (EndpointSourceStandard.sourceStandard D large hol c).val y g := rfl

theorem defectFamily_eq (side : Side) (q : RationalGL3) (K : ℕ) (r : ℝ × ℝ)
    (y : Fin 3 → RationalGL3) :
    defectFamily large D hol c side q K r y =
      eisensteinValue D hol c (GlobalEisensteinCocycle.realVertices y)
          (atInfinity (sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) *
            rationalGroup q⁻¹) -
        (sideSource large D hol c side).val (GlobalEisensteinCocycle.realVertices y)
          (atInfinity (sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) *
            rationalGroup q⁻¹) := rfl

end Defect

/-! ## Continuity of the plane Eisenstein summand -/

theorem sectionEisensteinValue_continuous {n : ℕ} (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D) (large : 4 ≤ n)
    (s : SectionSpace.inducedSections D .plane cohomologicalPoint) :
    Continuous (SectionSpace.sectionEisensteinValue D hol s).val := by
  set fam := SectionSpace.linearFlatExtension D hol s
  obtain ⟨bound, -, bounded⟩ :=
    CompactScalarRealization.flat_uniform_binary_bound D fam.val fam.property
  have halfPlane : -(n : ℝ) / 2 < cohomologicalPoint.re := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast large
    norm_num [cohomologicalPoint]; linarith
  rw [continuous_iff_continuousAt]
  intro g
  have h := NormalConvergence.continuousAt_halfPlane D fam.val fam.property bound
    (fun k hk b => bounded cohomologicalPoint k hk b) cohomologicalPoint g halfPlane
  have hc : ContinuousAt (fun x : AdelicGL => (cohomologicalPoint, x)) g :=
    (continuous_const.prodMk continuous_id).continuousAt
  refine (h.comp hc).congr ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  simp only [Function.comp]
  rw [EndpointEisensteinCocycle.sectionEisensteinValue_eq_sum D hol large s x]
  simp only [eisensteinSummand, fam, SectionSpace.linearFlatExtension_endpoint]

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
