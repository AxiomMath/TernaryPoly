module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticLattice
public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticBinaryShape

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpacePositive SymmetricSpaceParabolicCoordinates SymmetricSpaceFlagCoordinates
open SymmetricSpaceBorelCorner SymmetricSpaceRationalGluing SymmetricSpacePlaneBordification
open SymmetricSpaceFlagPlaneHomeomorph

/-- Actual plane parameters reconstruct exactly the original real matrix. -/
theorem planeParameters_matrix (r : PlaneGroup) :
    r.val.val=blockMatrix (planeParametersHom r).A.val (planeParametersHom r).u (planeParametersHom r).d.val := by
  exact (congrArg (fun g : RealGL => g.val) (planeParametersHom_matrix r)).symm

/-- A fixed matrix denominator bounds both the plane scalar and binary determinant. -/
theorem plane_scalar_det_bounds (d : ℕ) (hd : d≠0) (D : ℝ) (hD : 0<D) :
    ∃ F E : ℝ,0<F ∧ 0<E ∧ ∀ r : PlaneGroup,HasIntegralDenominator d r.val →
      |r.val.val.det|≤D → |(planeParametersHom r).d.val|≤F ∧ |(planeParametersHom r).A.val.det|≤E := by
  let ε : ℝ := 1/(d : ℝ)
  let η : ℝ := 1/((d^2 : ℕ) : ℝ)
  have hε : 0<ε := one_div_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hd)
  have hη : 0<η := one_div_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (pow_ne_zero 2 hd))
  refine ⟨D/η,D/ε,div_pos hD hη,div_pos hD hε,?_⟩
  intro r hr hdet
  let P := planeParametersHom r
  have hscalar : ε≤|P.d.val| := by
    have hm : r.val.val 2 2=P.d.val := by rw [planeParameters_matrix]; rfl
    exact real_denominator_lower_bound d hd _ P.d.ne_zero (by simpa only [hm] using hr 2 2)
  have hbinary : η≤|P.A.val.det| := by
    have hm : r.val.val 0 0*r.val.val 1 1-r.val.val 0 1*r.val.val 1 0=P.A.val.det := by
      rw [planeParameters_matrix]
      change P.A.val 0 0*P.A.val 1 1-P.A.val 0 1*P.A.val 1 0=P.A.val.det
      exact (det_fin_two _).symm
    exact real_denominator_lower_bound (d^2) (pow_ne_zero 2 hd) _ P.A.det_ne_zero
      (by simpa only [hm] using minor_denominator d r.val hr 0 0 1 1)
  have hprod : |P.A.val.det| * |P.d.val|≤D := by
    rw [planeParameters_matrix,blockMatrix_det,abs_mul] at hdet
    exact hdet
  constructor
  · apply (le_div_iff₀ hη).mpr
    exact (mul_le_mul_of_nonneg_left hbinary (abs_nonneg P.d.val)).trans
      (by simpa only [mul_comm] using hprod)
  · apply (le_div_iff₀ hε).mpr
    exact (mul_le_mul_of_nonneg_left hscalar (abs_nonneg P.A.val.det)).trans hprod

/-- A point of the plane overlap lies in the full chosen transition domain. -/
def planeTransitionPoint (r : PlaneGroup) (p : OverlapDomain) : domain r.val :=
  ⟨p.val,(mem_domain_iff r.val p.val).mpr ⟨Or.inl p.property,Or.inr r.property⟩⟩

/-- The chosen full transition agrees with the actual plane-overlap action. -/
theorem transition_plane (r : PlaneGroup) (p : OverlapDomain) :
    (transition r.val (planeTransitionPoint r p)).val=(planeModelMap r p).val := by
  have hd : DenseRange (liftInterior overlapDomain (fun _ hp => hp.1)) :=
    denseRange_liftInterior overlapDomain (fun _ hp => hp.1)
  have h : (fun q : OverlapDomain => (transition r.val (planeTransitionPoint r q)).val)=
      (fun q : OverlapDomain => (planeModelMap r q).val) :=
    hd.equalizer (continuous_subtype_val.comp ((transition r.val).continuous.comp
      (continuous_subtype_val.subtype_mk _)))
      (continuous_subtype_val.comp (planeModelMap r).continuous) (by
        funext S
        change (transition r.val (interiorPoint r.val S)).val=
          (planeModelMap r ⟨cornerEmbedding S,(cornerHomeomorph S).property.1⟩).val
        rw [transition_interiorPoint,planeModelMap_embedding])
  exact congrFun h p

/-- Every actual plane transition gives the exact full plane-bordification coordinate equation. -/
theorem plane_overlap_relation (r : PlaneGroup) (p : domain r.val)
    (hp : 0<p.val.2.1.val) :
    planeOverlap ⟨(transition r.val p).val,(transition_pos1_iff r.val p).mpr hp⟩=
      planeExtend r (planeOverlap ⟨p.val,hp⟩) := by
  have he : planeModelMap r ⟨p.val,hp⟩=
      ⟨(transition r.val p).val,(transition_pos1_iff r.val p).mpr hp⟩ := by
    apply Subtype.ext
    exact (transition_plane r ⟨p.val,hp⟩).symm
  have h := planeModelMap_commute r ⟨p.val,hp⟩
  rw [he] at h
  exact h

end TernaryPoly.SymmetricSpaceGluedArithmetic
