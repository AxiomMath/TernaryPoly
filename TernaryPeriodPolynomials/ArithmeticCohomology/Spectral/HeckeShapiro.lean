module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.StabilizerRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryHeckeDescent.Helpers

@[expose] public section


/-!
# Hecke operators in Shapiro coordinates

Let `F` be a point of a `G(ℚ)`-set `X` (a rational flag) and `t` a finite double-coset
correspondence of the arithmetic level `Γ`. Suppose that for every representative `r` of `ΓgΓ/Γ`
the point `r⁻¹F` lies in the `Γ`-orbit of `F`, say `r⁻¹F = γ_r F`. Then the elements `s_r = r γ_r`
fix `F`, their cosets `s_r Λ` (`Λ = Γ_F` the stabilizer) are disjoint and permuted by `Λ`, and
the Shapiro coordinate at `F` of the Hecke image of an ARBITRARY class is the local Hecke image:
`fixedPointH2 F (T_t w) = T_{S_t}(fixedPointH2 F w)`.

For away-from-three correspondences and the four cusp representatives this is used to diagonalize
the action of `awayThreeHeckeAlgebra` on the boundary in Shapiro coordinates.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Spectral.HeckeShapiro

open LocalHecke

variable {X : Type} [MulAction RationalGL3 X]

/-- The hypothesis that every representative moves `point` back into its own orbit. -/
def Transports (t : HeckeCorrespondence) (point : X) : Prop :=
  ∀ r ∈ t.representatives, ∃ γ : rationalLevel, γ.val • point = r⁻¹ • point

variable {t : HeckeCorrespondence} {point : X}

/-- The chosen element `γ_r` of the arithmetic level with `γ_r F = r⁻¹F`. -/
def transporter (transports : Transports t point) (r : RationalGL3) : RationalGL3 := by
  classical
  exact if h : r ∈ t.representatives then (transports r h).choose.val else 1

theorem transporter_mem (transports : Transports t point) (r : RationalGL3) :
    transporter transports r ∈ rationalLevel := by
  classical
  unfold transporter
  split_ifs with h
  · exact (transports r h).choose.property
  · exact rationalLevel.one_mem

theorem transporter_smul (transports : Transports t point) {r : RationalGL3}
    (hr : r ∈ t.representatives) : transporter transports r • point = r⁻¹ • point := by
  classical
  unfold transporter
  rw [dite_eq_left hr]
  exact (transports r hr).choose_spec

/-- The element `s_r = r γ_r`, which fixes the point. -/
def shifted (transports : Transports t point) (r : RationalGL3) : RationalGL3 :=
  r * transporter transports r

theorem shifted_smul (transports : Transports t point) {r : RationalGL3}
    (hr : r ∈ t.representatives) : shifted transports r • point = point := by
  rw [shifted, mul_smul, transporter_smul transports hr, smul_inv_smul]

theorem shifted_injOn (transports : Transports t point) :
    Set.InjOn (shifted transports) t.representatives := by
  intro r hr r' hr' heq
  apply t.disjoint r hr r' hr'
  have hr' : r' = r * transporter transports r * (transporter transports r')⁻¹ := by
    have h : r * transporter transports r = r' * transporter transports r' := heq
    rw [h]; group
  have hfinal : r⁻¹ * r' = transporter transports r * (transporter transports r')⁻¹ := by
    conv_lhs => rw [hr']
    group
  rw [hfinal]
  exact rationalLevel.mul_mem (transporter_mem transports r)
    (rationalLevel.inv_mem (transporter_mem transports r'))

/-- The local correspondence `S_t = {s_r}` on the stabilizer of the point. -/
def localCorrespondence (transports : Transports t point) :
    LocalCorrespondence (fixedPointLevel rationalLevel point) := by
  classical
  exact
  { representatives := t.representatives.image (shifted transports)
    stable := by
      intro element helement s hs
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨target, htarget, hlevel⟩ :=
        TernaryPeriodPolynomials.BoundaryHeckeDescent.Helpers.representative_exists t
          ⟨element, helement.1⟩⁻¹ ⟨r, hr⟩
      refine ⟨shifted transports target, Finset.mem_image_of_mem _ htarget, ?_, ?_⟩
      · have heq : (shifted transports target)⁻¹ * (element * shifted transports r) =
            (transporter transports target)⁻¹ * (target⁻¹ * (element * r)) *
              transporter transports r := by
          simp only [shifted]; group
        rw [heq]
        simp only [Subgroup.coe_inv, inv_inv] at hlevel
        exact rationalLevel.mul_mem (rationalLevel.mul_mem
          (rationalLevel.inv_mem (transporter_mem transports target)) hlevel)
          (transporter_mem transports r)
      · apply MulAction.mem_stabilizer_iff.mpr
        rw [mul_smul, mul_smul, shifted_smul transports hr,
          MulAction.mem_stabilizer_iff.mp helement.2, inv_smul_eq_iff,
          shifted_smul transports htarget]
    disjoint := by
      intro s hs s' hs' hmem
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨r', hr', rfl⟩ := Finset.mem_image.mp hs'
      have hlevel := hmem.1
      have hrr : r = r' := by
        apply t.disjoint r hr r' hr'
        have heq : r⁻¹ * r' = transporter transports r *
            ((shifted transports r)⁻¹ * shifted transports r') *
              (transporter transports r')⁻¹ := by
          simp only [shifted]; group
        rw [heq]
        exact rationalLevel.mul_mem (rationalLevel.mul_mem (transporter_mem transports r)
          hlevel) (rationalLevel.inv_mem (transporter_mem transports r'))
      rw [hrr] }

theorem localCorrespondence_representatives (transports : Transports t point)
    [DecidableEq RationalGL3] :
    (localCorrespondence transports).representatives =
      t.representatives.image (shifted transports) := by
  unfold localCorrespondence
  convert rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- **Cochain-level Shapiro–Hecke formula.** The value at the point of the double-coset sum of an
arbitrary cochain is the local Hecke sum of its restriction to the stabilizer. -/
theorem heckeCochain_apply_point (rho : Representation ℂ RationalGL3 V)
    (transports : Transports t point)
    (cochain : cochains rationalLevel (functionRepresentation rho X) 2)
    (vertices : Fin 3 → RationalGL3) :
    heckeCochain (functionRepresentation rho X) t cochain vertices point =
      ∑ s ∈ (localCorrespondence transports).representatives,
        rho s (cochain.val (fun index => s⁻¹ * vertices index) point) := by
  classical
  rw [localCorrespondence_representatives, Finset.sum_image (shifted_injOn transports)]
  unfold heckeCochain
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro r hr
  change rho r (cochain.val (fun index => r⁻¹ * vertices index) (r⁻¹ • point)) = _
  have hequivariant := congrFun (cochain.property
    ⟨(transporter transports r)⁻¹, rationalLevel.inv_mem (transporter_mem transports r)⟩
    (fun index => r⁻¹ * vertices index)) point
  change cochain.val (fun index => (transporter transports r)⁻¹ * (r⁻¹ * vertices index)) point =
    rho (transporter transports r)⁻¹
      (cochain.val (fun index => r⁻¹ * vertices index)
        ((transporter transports r)⁻¹⁻¹ • point)) at hequivariant
  rw [inv_inv, transporter_smul transports hr] at hequivariant
  have hvertices : (fun index => (shifted transports r)⁻¹ * vertices index) =
      (fun index => (transporter transports r)⁻¹ * (r⁻¹ * vertices index)) := by
    funext index
    simp only [shifted, mul_inv_rev, mul_assoc]
  rw [hvertices, hequivariant, shifted, map_mul, Module.End.mul_apply,
    ← Module.End.mul_apply (rho (transporter transports r)), ← map_mul, mul_inv_cancel,
    map_one, Module.End.one_apply]

/-- **Shapiro–Hecke formula on cohomology.** For any cohomology action realizing the double-coset
formula, the Shapiro coordinate at the point of `T_t w` is the local Hecke operator applied to the
Shapiro coordinate of `w`, for every class `w`. -/
theorem fixedPointH2_hecke (rho : Representation ℂ RationalGL3 V)
    (T : HeckeCorrespondence → Module.End ℂ (H2 rationalLevel (functionRepresentation rho X)))
    (hT : RealizesHecke (functionRepresentation rho X) T)
    (transports : Transports t point)
    (w : H2 rationalLevel (functionRepresentation rho X)) :
    fixedPointH2 rationalLevel rho point (T t w) =
      cohomologyAction rho (localCorrespondence transports)
        (fixedPointH2 rationalLevel rho point w) := by
  induction w using Submodule.Quotient.induction_on with
  | _ cocycle =>
  obtain ⟨image, himage, haction⟩ := hT t cocycle
  change fixedPointH2 rationalLevel rho point
      (T t (classOf rationalLevel (functionRepresentation rho X) cocycle)) = _
  rw [haction, fixedPointH2_classOf]
  change _ = cohomologyAction rho (localCorrespondence transports)
    (fixedPointH2 rationalLevel rho point
      (classOf rationalLevel (functionRepresentation rho X) cocycle))
  rw [fixedPointH2_classOf, cohomologyAction_classOf]
  apply congrArg
  apply Subtype.ext
  apply Subtype.ext
  funext vertices
  change image.val.val vertices point = _
  rw [himage]
  exact heckeCochain_apply_point rho transports cocycle.val vertices

end TernaryPeriodPolynomials.Spectral.HeckeShapiro
