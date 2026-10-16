module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Level.ChangeMackey

@[expose] public section


/-!
# Restriction of an induced class along a homomorphism, and the Mackey coordinates of a class with a given Shapiro coordinate

Formalized by Claude Sonnet 5.5.

* `ind_coord`: if `PhiH c_V = c` then the `uΔ`-coordinate of `res_K c_V` is the pull-back `κ_u^* c` (`exists_ind_class` plus injectivity of `PhiH`).
* `res_hom_eq_zero`: the restriction of `c_V` along any homomorphism `α : H → G` vanishes as soon as the restriction to the image `α.range` does (the
  restriction factors through the range), and the restriction to a subgroup `K` vanishes as soon as all Mackey coordinates `κ_u^* c` on `stabAt Δ K u` vanish
  (`res_eq_zero_of_pullbacks`, for `Δ` of finite index).
-/

open CategoryTheory GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

section Coord

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (Δ : Subgroup G)

/-- Every class with Shapiro coordinate `c` has the Mackey coordinates of `exists_ind_class`. -/
theorem ind_coord (c : groupCohomology.H2 (Rep.of (ρ.comp Δ.subtype))) (cV : groupCohomology.H2 (Rep.of (permRep ρ Δ)))
    (hcV : PhiH ρ Δ cV = c) (K : Subgroup G) (u : G) (hu : ∀ k ∈ K, u⁻¹ * k * u ∈ Δ) :
    coordH ρ Δ K u hu (twoCohomologyRestriction K.subtype (Rep.of (permRep ρ Δ)) cV) =
      EdgeNat.h2Map (kappa Δ K u hu) (Rep.of (ρ.comp Δ.subtype)) (Rep.of (ρ.comp K.subtype)) (ρ u)
        (kappa_hT ρ Δ K u hu) c := by
  obtain ⟨cV', h'⟩ := exists_ind_class ρ Δ c
  have h1 : PhiH ρ Δ cV' = c := by
    have := h' Δ 1 (fun k hk => by simpa using hk)
    exact this.trans (h2Map_kappa_one ρ Δ c)
  have : cV = cV' := PhiH_injective ρ Δ (hcV.trans h1.symm)
  subst this
  exact h' K u hu

end Coord

section Hom

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (Δ : Subgroup G)
  {H : Type} [Group H] (α : H →* G)

/-- The restriction of a class along `α` vanishes if its restriction to the range of `α` does. -/
theorem res_hom_eq_zero (cV : groupCohomology.H2 (Rep.of (permRep ρ Δ)))
    (h : twoCohomologyRestriction α.range.subtype (Rep.of (permRep ρ Δ)) cV = 0) :
    twoCohomologyRestriction α (Rep.of (permRep ρ Δ)) cV = 0 := by
  have hα : α.range.subtype.comp α.rangeRestrict = α := MonoidHom.subtype_comp_rangeRestrict α
  have e1 := h2Map_comp α.range.subtype α.rangeRestrict (Rep.of (permRep ρ Δ)) (Rep.res α.range.subtype (Rep.of (permRep ρ Δ)))
    (Rep.res α (Rep.of (permRep ρ Δ))) LinearMap.id (fun _ _ => rfl) LinearMap.id (fun _ _ => rfl) cV
  rw [twoCohomologyRestriction_eq_h2Map] at h
  rw [h, map_zero] at e1
  rw [twoCohomologyRestriction_eq_h2Map]
  exact (h2Map_congr hα.symm _ _ _ _ (LinearMap.ext fun _ => rfl) cV).trans e1.symm

/-- **Vanishing of the restriction of an induced class along a homomorphism from the pull-backs on the Mackey subgroups of its range.** -/
theorem res_hom_eq_zero_of_pullbacks [Finite (G ⧸ Δ)] (c : groupCohomology.H2 (Rep.of (ρ.comp Δ.subtype)))
    (cV : groupCohomology.H2 (Rep.of (permRep ρ Δ))) (hcV : PhiH ρ Δ cV = c)
    (hz : ∀ u : G, EdgeNat.h2Map (kappa Δ (stabAt Δ α.range u) u (stabAt_hu Δ α.range u)) (Rep.of (ρ.comp Δ.subtype))
      (Rep.of (ρ.comp (stabAt Δ α.range u).subtype)) (ρ u) (kappa_hT ρ Δ (stabAt Δ α.range u) u (stabAt_hu Δ α.range u)) c = 0) :
    twoCohomologyRestriction α (Rep.of (permRep ρ Δ)) cV = 0 := by
  have : Fintype (MulAction.orbitRel.Quotient ↥α.range (G ⧸ Δ)) := Fintype.ofFinite _
  refine res_hom_eq_zero ρ Δ α cV (res_eq_zero_of_coords ρ Δ α.range cV fun u => ?_)
  rw [ind_coord ρ Δ c cV hcV _ u (stabAt_hu Δ α.range u)]
  exact hz u

end Hom

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
