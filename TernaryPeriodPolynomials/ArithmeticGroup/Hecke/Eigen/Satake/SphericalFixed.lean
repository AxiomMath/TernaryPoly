module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.DistinctData

@[expose] public section


/-!
# Spherical cuspidal representations have nonzero away-from-three fixed vectors

A `SphericalCusp` vector is fixed by `GL₂(Ẑ)`, hence by the away-from-three level `K3`. So the
standing hypothesis `Nontrivial (fixedVectors σ K3)` of the Satake results holds automatically for
spherical cusp data. In particular the independence results apply unconditionally to spherical data.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.RepresentationTheory

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

theorem fixedVectors_nontrivial_of_spherical (σ : CuspidalRepresentation)
    (hσ : SphericalCusp σ) : Nontrivial (fixedVectors σ K3) := by
  obtain ⟨v, hv0, hfix⟩ := hσ
  refine ⟨⟨⟨v.val, ?_⟩, 0, ?_⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hk
    obtain ⟨c, rfl⟩ := awayLevel_le_spherical placeThree hb
    exact hfix c
  · intro h
    apply hv0
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this

/-- **Spherical independence.** For spherical cusp data with the same character, different
`ω(diag(p,1))` at some `p ≠ 3` forces independent associate pairs. -/
theorem associatePair_inf_eq_bot_of_omega_ne_spherical {n p : ℕ} (σ σ' : CuspidalRepresentation)
    (hσ : SphericalCusp σ) (hσ' : SphericalCusp σ') (χ : RankOneCharacter)
    (coh : Cohomological σ n) (coh' : Cohomological σ' n)
    (hp : p.Prime) (h3 : p ≠ 3) (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP hp)
    (hecke : BoundaryHecke n χ) (hhecke : ActualBoundaryHecke n χ hecke)
    (hω : omega σ (Bo (dP hp)) ≠ omega σ' (Bo (dP hp))) :
    associatePair (⟨σ, χ, coh⟩ : InducingData n) ⊓
      associatePair (⟨σ', χ, coh'⟩ : InducingData n) = ⊥ := by
  have := fixedVectors_nontrivial_of_spherical σ hσ
  have := fixedVectors_nontrivial_of_spherical σ' hσ'
  exact associatePair_inf_eq_bot_of_omega_ne σ σ' χ coh coh' hp h3 t ht hg hecke hhecke hω

/-- A spherical cuspidal representation has a nonzero smooth vector. -/
theorem smooth_nonzero_of_spherical (σ : CuspidalRepresentation) (hσ : SphericalCusp σ) :
    ∃ v ∈ σ.smooth, v ≠ 0 := by
  obtain ⟨v, hv0, -⟩ := hσ
  refine ⟨v.val, v.property, fun h => hv0 (Subtype.ext h)⟩

/-- **Spherical `diag(p,p,1)` plane eigenvalue**, with all standing hypotheses discharged. -/
theorem plane_Tp2_eq_cusp_spherical {n p : ℕ} (D : InducingData n) (hD : SphericalCusp D.cusp)
    (hp : p.Prime) (h3 : p ≠ 3) (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP2 hp)
    (f : AdelicGL → ℂ) (hf : IsInduced D .plane cohomologicalPoint f) (g : AdelicGL) :
    ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
      cuspPlaneEigenvalue2 D hp * f g := by
  have := fixedVectors_nontrivial_of_spherical D.cusp hD
  exact prime2_plane_eigenvalue_cohomological D hp h3 t ht hg
    (smooth_nonzero_of_spherical D.cusp hD) f hf g

/-- **Spherical `T_p` eigenvalue** on plane and line induced sections. -/
theorem Tp_eq_cusp_spherical {n p : ℕ} (D : InducingData n) (hD : SphericalCusp D.cusp)
    (hp : p.Prime) (h3 : p ≠ 3) (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP hp)
    (side : Side) (f : AdelicGL → ℂ) (hf : IsInduced D side cohomologicalPoint f)
    (g : AdelicGL) :
    ∑ r ∈ t.representatives, f (g * atFinite (rationalFinite r)) =
      cuspPlaneEigenvalue D hp * f g := by
  have := fixedVectors_nontrivial_of_spherical D.cusp hD
  cases side
  · exact plane_Tp_eq_cusp D hp h3 t ht hg f hf g
  · exact line_Tp_eq_cusp D hp h3 t ht hg f hf g

end TernaryPeriodPolynomials.HeckeEigen.Satake
