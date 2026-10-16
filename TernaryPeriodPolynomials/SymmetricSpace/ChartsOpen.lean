module

public import TernaryPeriodPolynomials.SymmetricSpace.ChartsBasic
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpaceCharts
open SymmetricSpacePositive

abbrev Vector := Fin 3 → ℝ
abbrev UnitSphere := Metric.sphere (0 : Vector) 1

/-- The actual real quadratic form attached to a matrix, on the finite real vector space. -/
def quadratic (S : Mat) (v : Vector) : ℝ := v ⬝ᵥ (S *ᵥ v)

theorem quadratic_smul (S : Mat) (r : ℝ) (v : Vector) :
    quadratic S (r • v)=r^2*quadratic S v := by
  simp only [quadratic,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

theorem unitSphere_ne_zero (v : UnitSphere) : v.val≠0 := by
  have hn : dist v.val 0=1 := v.property
  rw [dist_zero_right] at hn
  intro h
  simp [h] at hn

/-- Testing the compact unit sphere is equivalent to testing all nonzero real vectors. -/
theorem posDef_iff_unitSphere (S : Mat) (hS : S.IsHermitian) :
    S.PosDef ↔ ∀ v : UnitSphere,0<quadratic S v.val := by
  constructor
  · intro h v
    simpa [quadratic] using h.dotProduct_mulVec_pos (unitSphere_ne_zero v)
  · intro h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hS
    intro v hv
    have hn : ‖(‖v‖⁻¹ : ℝ) • v‖=1 := norm_smul_inv_norm hv
    have hm : (‖v‖⁻¹ : ℝ) • v∈Metric.sphere (0 : Vector) 1 := by
      simpa [Metric.mem_sphere,dist_zero_right] using hn
    have hp := h ⟨(‖v‖⁻¹ : ℝ) • v,hm⟩
    change 0<quadratic S ((‖v‖⁻¹ : ℝ) • v) at hp
    rw [quadratic_smul] at hp
    have hc : 0<(‖v‖⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv))
    have hq : 0<quadratic S v := (mul_pos_iff_of_pos_left hc).mp hp
    simpa [quadratic] using hq

theorem continuous_quadratic_on_sphere :
    Continuous (fun p : Coordinates × UnitSphere => quadratic (reconstruct p.1) p.2.val) := by
  have hv : Continuous (fun p : Coordinates × UnitSphere => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact hv.dotProduct ((continuous_reconstruct.comp continuous_fst).matrix_mulVec hv)

/-- Positivity is open in the five coordinates, proved from compactness of the unit sphere.
The excluded set is the closed projection of the locus where a unit vector has nonpositive energy. -/
theorem isOpen_positiveCoordinates : IsOpen positiveCoordinates := by
  let bad : Set (Coordinates × UnitSphere) :=
    {p | quadratic (reconstruct p.1) p.2.val≤0}
  have hbad : IsClosed bad := isClosed_le continuous_quadratic_on_sphere continuous_const
  have hproj : IsClosed (Prod.fst '' bad) := isClosedMap_fst_of_compactSpace bad hbad
  have heq : positiveCoordinates=(Prod.fst '' bad)ᶜ := by
    ext x
    change (reconstruct x).PosDef ↔ x∉Prod.fst '' bad
    constructor
    · intro hx himage
      obtain ⟨⟨y,v⟩,hy,hxy⟩ := himage
      change y=x at hxy
      subst y
      exact (not_le_of_gt ((posDef_iff_unitSphere _ (reconstruct_isHermitian x)).mp hx v)) hy
    · intro hx
      apply (posDef_iff_unitSphere _ (reconstruct_isHermitian x)).mpr
      intro v
      by_contra hv
      exact hx ⟨(x,v),le_of_not_gt hv,rfl⟩
  rw [heq]
  exact hproj.isOpen_compl

end TernaryPoly.SymmetricSpaceCharts
