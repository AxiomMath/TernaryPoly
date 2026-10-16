module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineCosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneLocalOp
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneCoordinate

@[expose] public section


/-!
# `localOp` of `T_p` at the bad-line cusp

The reference bad-line cusp `cuspFlag .line false` is the standard flag `QuotientGroup.mk 1`. For
every away-from-three correspondence `t` of `Γ diag(p,1,1) Γ` (`p ≠ 3`), the local correspondence of
`t` at this cusp has the same cosets `sΛ` as the explicit `badLineCosets p`: every explicit
representative lies in the double coset (explicit factorizations `a · diag(p,1,1) · b` with `a, b`
in the level) and both sets have `p² + p + 1` elements. Hence `localOp t` is the explicit local
operator (`localOp_badLine`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineLocalOp

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.HeckeEigen.Satake
open LineCoordinates IdentityPlaneCosets LevelOneCosets LevelThreeCosets BadLineCoordinates
open BadLineCosets IdentityPlaneLocalOp IdentityPlaneCoordinate CuspOrbits CuspReduction
open LocalHecke AmbientHecke
open GoodLineCosets (cvec)

variable (p : Nat.Primes)

/-! ### The explicit representatives lie in the double coset -/

theorem sLev_some_double (i : Fin p.val) :
    ∃ a b : rationalLevel, sLev p (some i) = a.val * gP p.property * b.val := by
  let Ma : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 0; 1, 0, -(i.val : ℤ); 0, 0, 1]
  let Mb : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 0; 1, 0, 0; 0, 0, 1]
  have hda : IsUnit Ma.det := by
    have : Ma.det = -1 := by simp [Ma, Matrix.det_fin_three]
    rw [this]; exact isUnit_one.neg
  have hdb : IsUnit Mb.det := by
    have : Mb.det = -1 := by simp [Mb, Matrix.det_fin_three]
    rw [this]; exact isUnit_one.neg
  have hra : ∀ j, ((Ma 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j; fin_cases j <;> simp [Ma]
  have hrb : ∀ j, ((Mb 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j; fin_cases j <;> simp [Mb]
  refine ⟨lvl Ma hda hra, lvl Mb hdb hrb, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, lvl_val, lvl_val, gP_val, sLev, R_val, BQ_val]
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [Ma, Mb, Matrix.mul_apply, Fin.sum_univ_three, Bl, vmul]

theorem sLev_none_double (hp3 : p.val ≠ 3) :
    ∃ a b : rationalLevel, sLev p none = a.val * gP p.property * b.val := by
  have hcast : ((((signP p : ℤˣ) : ℤ) * p.val : ℤ) : ZMod 3) = 1 := by
    push_cast
    rw [signP_cast p hp3]
    exact cast_mul_self p hp3
  have hdvd : (3 : ℤ) ∣ 1 - ((signP p : ℤˣ) : ℤ) * p.val := by
    have h0 : (((1 - ((signP p : ℤˣ) : ℤ) * p.val : ℤ)) : ZMod 3) = 0 := by
      push_cast at hcast ⊢
      rw [hcast, sub_self]
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h0
  obtain ⟨β, hβ⟩ := hdvd
  let Ma : Matrix (Fin 3) (Fin 3) ℤ :=
    !![1, 0, -β; 0, ((signP p : ℤˣ) : ℤ), 0; 3, 0, ((signP p : ℤˣ) : ℤ) * p.val]
  let Mb : Matrix (Fin 3) (Fin 3) ℤ :=
    !![((signP p : ℤˣ) : ℤ), 0, β * ((signP p : ℤˣ) : ℤ); 0, 1, 0;
      -3, 0, ((signP p : ℤˣ) : ℤ) * p.val]
  have hdetA : Ma.det = ((signP p : ℤˣ) : ℤ) := by
    simp only [Ma, Matrix.det_fin_three]
    simp
    first
    | linear_combination (-((signP p : ℤˣ) : ℤ)) * hβ
  have hdetB : Mb.det = ((signP p : ℤˣ) : ℤ) := by
    simp only [Mb, Matrix.det_fin_three]
    simp
    first
    | linear_combination (-((signP p : ℤˣ) : ℤ)) * hβ
  have hunit : IsUnit ((signP p : ℤˣ) : ℤ) := (signP p).isUnit
  have hda : IsUnit Ma.det := by rw [hdetA]; exact hunit
  have hdb : IsUnit Mb.det := by rw [hdetB]; exact hunit
  have hra : ∀ j, ((Ma 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j; fin_cases j
    · exact zmod_three
    · simp [Ma]
    · simpa [Ma] using hcast
  have hrb : ∀ j, ((Mb 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j; fin_cases j
    · exact zmod_neg_three
    · simp [Mb]
    · simpa [Mb] using hcast
  refine ⟨lvl Ma hda hra, lvl Mb hdb hrb, ?_⟩
  have hβq : (3 : ℚ) * (β : ℚ) = 1 - (((signP p : ℤˣ) : ℤ) : ℚ) * p.val := by
    exact_mod_cast hβ.symm
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, lvl_val, lvl_val, gP_val, sLev, R_val, BQ_val]
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [Ma, Mb, Matrix.mul_apply, Fin.sum_univ_three, Bl, vmul] <;>
    first
    | ring1
    | linear_combination hβq
    | linear_combination (p.val : ℚ) * (((signP p : ℤˣ) : ℤ) : ℚ) * hβq
    | linear_combination (-((p.val : ℚ) * (((signP p : ℤˣ) : ℤ) : ℚ) + 1)) * hβq
    | linear_combination (-2 * (p.val : ℚ) * (((signP p : ℤˣ) : ℤ) : ℚ)) * hβq
    | linear_combination (-1) * hβq
    | linear_combination (-((p.val : ℚ) * (((signP p : ℤˣ) : ℤ) : ℚ))) * hβq

theorem sRad_double (c : Fin p.val × Fin p.val) :
    ∃ a b : rationalLevel, sRad p c = a.val * gP p.property * b.val := by
  let Ma : Matrix (Fin 3) (Fin 3) ℤ :=
    !![sgnP p, (cvec p c).1, (cvec p c).2; 0, 1, 0; 0, 0, 1]
  have hda : IsUnit Ma.det := by
    have : Ma.det = sgnP p := by simp [Ma, Matrix.det_fin_three]
    rw [this]; exact isUnit_sgnP p
  have hra : ∀ j, ((Ma 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j; fin_cases j <;> simp [Ma]
  refine ⟨lvl Ma hda hra, 1, ?_⟩
  have R1q : (p.val : ℚ) * (sgnP p : ℚ) = (epsP p : ℚ) := by exact_mod_cast sgnP_mul p
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, lvl_val, gP_val, sRad, R_val]
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [Ma, Matrix.mul_apply, Fin.sum_univ_three, icast, vmul, epsU_val]
  all_goals
    first
    | linear_combination R1q
    | linear_combination (-2) * R1q
    | linear_combination (-1) * R1q

/-- **Every explicit bad-line representative lies in `Γ diag(p,1,1) Γ`.** -/
theorem rExpl_double (hp3 : p.val ≠ 3) (i : BIdx p) :
    ∃ a b : rationalLevel, rExpl p i = a.val * gP p.property * b.val := by
  rcases i with (_ | j) | c
  · exact sLev_none_double p hp3
  · exact sLev_some_double p j
  · exact sRad_double p c

/-! ### `localOp` at the bad line -/

theorem R_fixes (w : ℚ × ℚ) (a : ℚˣ) (B : GL (Fin 2) ℚ) :
    R w a B ∈ MulAction.stabilizer RationalGL3 (QuotientGroup.mk 1 : Flags .line) := by
  rw [MulAction.mem_stabilizer_iff]
  change (QuotientGroup.mk (R w a B * 1) : Flags .line) = QuotientGroup.mk 1
  rw [QuotientGroup.eq, mul_one, mul_one]
  apply (parabolic .line).inv_mem
  change InLineParabolic (R w a B)
  constructor <;> simp [R_val]

theorem rExpl_fixes (i : BIdx p) :
    rExpl p i ∈ MulAction.stabilizer RationalGL3 (QuotientGroup.mk 1 : Flags .line) := by
  rcases i with j | c <;> exact R_fixes _ _ _

/-- **`localOp` of any `T_p` correspondence at the bad-line cusp is the explicit local operator.** -/
theorem localOp_badLine (n : ℕ) (t : HeckeCorrespondence) (ht : AwayThree t)
    (hg : t.g = gP p.property) (hp3 : p.val ≠ 3) :
    localOp n trivialCharacter t ht .line false =
      cohomologyAction (ρn n) (badLineCosets p hp3) := by
  classical
  have htr := transports_cuspFlag t ht .line false
  have hex : ∀ s : (badLineCosets p hp3).representatives,
      ∃ s' ∈ (HeckeShapiro.localCorrespondence htr).representatives, s.val⁻¹ * s' ∈ ΛB := by
    rintro ⟨s, hs⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨a, b, hab⟩ := rExpl_double p hp3 i
    obtain ⟨r, hr, hrl⟩ := t.complete a b
    rw [hg, ← hab] at hrl
    refine ⟨HeckeShapiro.shifted htr r, ?_, ?_⟩
    · rw [HeckeShapiro.localCorrespondence_representatives]
      exact Finset.mem_image_of_mem _ hr
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h := rationalLevel.mul_mem (rationalLevel.inv_mem hrl)
          (HeckeShapiro.transporter_mem htr r)
        convert h using 1
        simp only [HeckeShapiro.shifted]
        group
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (rExpl_fixes p i))
          (HeckeShapiro.shifted_smul htr hr)
  choose f hfmem hf using hex
  have hcard : (HeckeShapiro.localCorrespondence htr).representatives.card ≤
      (badLineCosets p hp3).representatives.card := by
    rw [HeckeShapiro.localCorrespondence_representatives]
    refine (Finset.card_image_le).trans ?_
    rw [card_representatives p.property t ht hg]
    change _ ≤ (Finset.univ.image (rExpl p)).card
    rw [Finset.card_image_of_injective _ (rExpl_injective p), Finset.card_univ, Fintype.card_sum,
      Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
    apply le_of_eq
    ring
  unfold localOp
  exact (cohomologyAction_eq_of_injective (ρn n) (badLineCosets p hp3)
    (HeckeShapiro.localCorrespondence htr) (fun s => ⟨f s, hfmem s⟩) hf hcard).symm

/-- The same for the `T_p` correspondence `TpExistence.tp p`, which exists for `p ≠ 3`. -/
theorem localOp_badLine_tp (n : ℕ) (hp3 : p.val ≠ 3) :
    localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .line false =
      cohomologyAction (ρn n) (badLineCosets p hp3) :=
  localOp_badLine p n _ _ (TpExistence.tp_g p) hp3

end TernaryPeriodPolynomials.LevelThree.BadLineLocalOp
