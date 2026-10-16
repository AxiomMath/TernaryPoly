module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Flag.Orbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Gamma6.Stokes

@[expose] public section


/-!
# Zero flag restrictions of a global class give a vanishing flag component

Formalized by Claude Sonnet 5.5.

If a class `c` of `H²(Γ(6), E)` restricts to zero on every flag group `Γ(6) ∩ g⁻¹Bg`, then its geometric representative `X` in the point resolution has vanishing pullback to the
resolution of the complete flags: the Shapiro coordinate of the pullback at a flag `F_g` is the restriction of `c` to the stabilizer of `F_g`, which is the flag group.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.EquivariantSingularSmall
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open GeneralEisenstein

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section FlagGroup

/-- The embedding of the flag group `gammaNBAt 6 g` into `Γ(6)`. -/
def flagEmb (g : SL(3, ℤ)) : ↥(gammaNBAt 6 g) →* Γ6 :=
  (gammaSixEquiv : gammaN 6 →* Γ6).comp (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp))

theorem flagEmb_mem (g : SL(3, ℤ)) (p : gammaNBAt 6 g) : flagEmb g p ∈ MulAction.stabilizer Γ6 (flagOf g) :=
  (mem_stabilizer_flagOf_iff (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp) p) g).2 p.2

/-- The flag group as a subgroup of the stabilizer of the flag. -/
def flagAlpha (g : SL(3, ℤ)) : ↥(gammaNBAt 6 g) →* ↥(MulAction.stabilizer Γ6 (flagOf g)) :=
  (flagEmb g).codRestrict _ (flagEmb_mem g)

theorem flagAlpha_bijective (g : SL(3, ℤ)) : Function.Bijective (flagAlpha g) := by
  constructor
  · intro a b h
    have h1 : flagEmb g a = flagEmb g b := congrArg Subtype.val h
    exact gammaSixEquiv.injective.comp (Subgroup.inclusion_injective _) h1
  · intro s
    obtain ⟨p, hp⟩ := gammaSixEquiv.surjective s.1
    have hs := (mem_stabilizer_flagOf_iff p g).1 (hp ▸ s.2)
    refine ⟨⟨p.1, hs⟩, Subtype.ext ?_⟩
    exact hp

end FlagGroup

section Vanish

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
/-- The restriction of the transported class to the stabilizer of any flag vanishes, if the class restricts to zero on every flag group. -/
theorem res_stab_flag_zero (c : groupCohomology.H2 (Rep.of ρ))
    (hz : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp))
      (Rep.of ρ) c = 0) (F : Flag) :
    twoCohomologyRestriction (MulAction.stabilizer Γ6 F).subtype (Rep.of (rep6 ρ)) (toGamma6 ρ c) = 0 := by
  obtain ⟨g, rfl⟩ := exists_flagOf F
  have h0 := cmpH2_res ρ (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp)) c
  rw [hz g, map_zero] at h0
  -- `h0 : 0 = res_{flagEmb g} (toGamma6 c)`
  have hcomp : twoCohomologyRestriction ((MulAction.stabilizer Γ6 (flagOf g)).subtype.comp (flagAlpha g))
      (Rep.of (rep6 ρ)) (toGamma6 ρ c) = 0 := h0.symm
  rw [FacePairing.twoCohomologyRestriction_comp] at hcomp
  apply map_two_injective_of_bijective (flagAlpha g) (flagAlpha_bijective g)
  rw [map_zero]
  exact hcomp


omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
/-- The same for the dual coefficient module. -/
theorem res_stab_flag_zero_dual (c : groupCohomology.H2 (Rep.of ρ.dual))
    (hz : ∀ g : SL(3, ℤ), twoCohomologyRestriction (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp))
      (Rep.of ρ.dual) c = 0) (F : Flag) :
    twoCohomologyRestriction (MulAction.stabilizer Γ6 F).subtype (Rep.of (rep6 ρ).dual) (toGamma6Dual ρ c) = 0 := by
  obtain ⟨g, rfl⟩ := exists_flagOf F
  have h0 := cmpH2Dual_res ρ (Subgroup.inclusion (fun _ hp => gammaNBAt_le_gammaN 6 g hp)) c
  rw [hz g, map_zero] at h0
  have hcomp : twoCohomologyRestriction ((MulAction.stabilizer Γ6 (flagOf g)).subtype.comp (flagAlpha g))
      (Rep.of (rep6 ρ).dual) (toGamma6Dual ρ c) = 0 := h0.symm
  rw [FacePairing.twoCohomologyRestriction_comp] at hcomp
  apply map_two_injective_of_bijective (flagAlpha g) (flagAlpha_bijective g)
  rw [map_zero]
  exact hcomp

end Vanish

section General

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]

/-- **A class of `H²(Γ(6), σ)` restricting to zero on the stabilizer of every flag has a geometric representative with vanishing flag component.** -/
theorem exists_flag_vanishing_of_res (σ : Representation ℂ Γ6 V) (c : groupCohomology.H2 (Rep.of σ))
    (hres : ∀ F : Flag, twoCohomologyRestriction (MulAction.stabilizer Γ6 F).subtype (Rep.of σ) c = 0) :
    ∃ X : (homCochains (prodComplex Γ6 RationalGL3 PUnit) (qRep (MonoidHom.id Γ6) σ)).homology 2,
      (fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) (qRep (MonoidHom.id Γ6) σ) 2).hom X = qH2 σ c ∧
      (HomologicalComplex.homologyMap (homPullback (ptMap Flag) (qRep (MonoidHom.id Γ6) σ)) 2).hom X = 0 := by
  obtain ⟨X, hX⟩ := fixCoordH_pt_surjective (qRep (MonoidHom.id Γ6) σ) (qH2 σ c)
  refine ⟨X, hX, ?_⟩
  have hinj := (faceCoord_product_bijective (Γ := Γ6) (V := RationalGL3) (Z := Flag) (1 : RationalGL3)
    vertexAction_free' (qRep (MonoidHom.id Γ6) σ)).1
  apply hinj
  funext o
  have h := congrArg (fun m => m.hom X) (faceCoord_restriction (stabilizer Γ6 o.out)
    (qRep (MonoidHom.id Γ6) σ) (1 : RationalGL3) o.out (fun g => g.2) 2)
  have h' : (faceCoord (stabilizer Γ6 o.out) (qRep (MonoidHom.id Γ6) σ) (1 : RationalGL3) o.out
      (fun g => g.2) 2).hom
      ((HomologicalComplex.homologyMap (homPullback (ptMap Flag) (qRep (MonoidHom.id Γ6) σ)) 2).hom X) =
      (groupCohomology.map (stabilizer Γ6 o.out).subtype
        (𝟙 (Rep.res (stabilizer Γ6 o.out).subtype (qRep (MonoidHom.id Γ6) σ))) 2).hom
        ((fixCoordH (1 : RationalGL3) PUnit.unit (fun _ => rfl) (qRep (MonoidHom.id Γ6) σ) 2).hom X) := h
  change (faceCoord (stabilizer Γ6 o.out) (qRep (MonoidHom.id Γ6) σ) (1 : RationalGL3) o.out
      (fun g => g.2) 2).hom
      ((HomologicalComplex.homologyMap (homPullback (ptMap Flag) (qRep (MonoidHom.id Γ6) σ)) 2).hom X) =
    (faceCoord (stabilizer Γ6 o.out) (qRep (MonoidHom.id Γ6) σ) (1 : RationalGL3) o.out
      (fun g => g.2) 2).hom 0
  rw [h', hX, map_zero]
  have := qH2_map σ (stabilizer Γ6 o.out).subtype c
  refine Eq.trans this.symm ?_
  change qH2 (σ.comp (stabilizer Γ6 o.out).subtype)
    (twoCohomologyRestriction (stabilizer Γ6 o.out).subtype (Rep.of σ) c) = 0
  rw [hres o.out]
  exact map_zero _

end General

end TernaryPeriodPolynomials.Argument.GammaNStokes
