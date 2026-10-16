module

public import TernaryPeriodPolynomials.PeriodPolynomial.Apolar.Projectors
public import TernaryPeriodPolynomials.PeriodPolynomial.Apolar.FixedZero
public import TernaryPeriodPolynomials.Analysis.SelfAdjointProjectionSurjective

@[expose] public section

noncomputable section
namespace TernaryPoly.BinaryApolar
open BinaryFiniteInvariant

/-- An invariant killed by the odd projector is fixed by all three generators, hence zero. -/
theorem projector_disjoint (d : ℕ) (hd : Even d) (hpos : 0<d) (p : H d)
    (hq : invariantProjector d p=p) (hp : oddProjector d p=0) : p=0 := by
  have hi : p ∈ invariants d := (invariantProjector_isProj d).mem_iff_map_id.mpr hq
  have hSD : swap d (negateFirst d p)=negateFirst d p := by
    rw [←negateFirst_swap d hd,hi.1]
  have he : oddProjector d p=(1/2 : ℚ) • (p-negateFirst d p) := by
    rw [oddProjector_apply,hi.1,hSD]
    module
  rw [he] at hp
  have hz : p-negateFirst d p=0 := (smul_eq_zero.mp hp).resolve_left (by norm_num)
  exact three_fixed_zero hpos p hi.1 hi.2 (sub_eq_zero.mp hz).symm

/-- The actual order-three norm surjects in every positive even homogeneous degree. -/
theorem normMap_surjective (d : ℕ) (hd : Even d) (hpos : 0<d) :
    Function.Surjective (normMap d) := by
  have hsurj := SelfAdjointProjection.rangeRestrict_comp_surjective
    (form ℚ d) (separating_left ℚ d) (form_surjective ℚ d)
    (oddProjector d) (invariantProjector d)
    (oddProjector_adjoint d hd) (invariantProjector_adjoint d hd)
    (fun p => (invariantProjector_isProj d).map_id _ ((invariantProjector_isProj d).map_mem p))
    (projector_disjoint d hd hpos)
  intro q
  have hq : q.val ∈ (invariantProjector d).range := by
    rw [(invariantProjector_isProj d).range]
    exact q.property
  obtain ⟨v,hv⟩ := hsurj ⟨q.val,hq⟩
  have he : invariantProjector d (oddProjector d v)=q.val := congrArg Subtype.val hv
  let r : oddSymmetric d := ⟨(1/3 : ℚ) • oddProjector d v,
    (oddSymmetric d).smul_mem _ ((oddProjector_isProj d hd).map_mem v)⟩
  refine ⟨r,?_⟩
  apply Subtype.ext
  change norm d ((1/3 : ℚ) • oddProjector d v)=q.val
  rw [map_smul]
  have hs := ((oddProjector_isProj d hd).map_mem v).1
  have hsn := (norm_mem_invariants d (oddProjector d v) hs).1
  rw [invariantProjector_apply,hsn] at he
  calc
    (1/3 : ℚ) • norm d (oddProjector d v) =
        (1/6 : ℚ) • (norm d (oddProjector d v)+norm d (oddProjector d v)) := by module
    _ = q.val := he

end TernaryPoly.BinaryApolar
