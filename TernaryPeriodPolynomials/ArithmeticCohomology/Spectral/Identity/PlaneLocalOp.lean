module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.PrimeCount
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.Involution
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.TpExistence

@[expose] public section


/-!
# `localOp` of `T_p` at the identity-plane cusp

For every away-from-three Hecke correspondence `t` of the double coset `Γ diag(p,1,1) Γ`, the
local correspondence of `t` at the identity plane (`HeckeShapiro.localCorrespondence`) has the same
cosets `sΛ₀` as the explicit `identityPlaneCosets p`: every explicit representative lies in the
double coset (explicit factorizations `a · diag(p,1,1) · b` with `a, b` in the level) and both sets
have `p² + p + 1` elements. Hence `localOp t` equals the explicit local operator, and the binary edge
intertwines it with `1 + p^{-(n+2)} T_p` (`edgeH2_localOp`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.IdentityPlaneLocalOp

open LocalHecke

/-! ### Local correspondences with the same cosets -/

section Generic

variable {G : Type} [Group G] {level : Subgroup G} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cochainAction_eq_of_equiv (rho : Representation ℂ G V) (S S' : LocalCorrespondence level)
    (e : S.representatives ≃ S'.representatives) (he : ∀ s, s.val⁻¹ * (e s).val ∈ level)
    (degree : ℕ) : cochainAction rho S degree = cochainAction rho S' degree := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  rw [cochainAction_apply, cochainAction_apply, ← Finset.sum_coe_sort S.representatives,
    ← Finset.sum_coe_sort S'.representatives]
  refine Fintype.sum_equiv e _ _ (fun s => ?_)
  let l : level := ⟨s.val⁻¹ * (e s).val, he s⟩
  have hx : (fun index => (e s).val⁻¹ * x index) = fun index => l⁻¹.val * (s.val⁻¹ * x index) := by
    funext index
    simp only [l, Subgroup.coe_inv]
    group
  rw [hx, f.property l⁻¹ (fun index => s.val⁻¹ * x index), ← Module.End.mul_apply, ← map_mul]
  congr 2
  simp only [l, Subgroup.coe_inv]
  group

theorem cohomologyAction_eq_of_equiv (rho : Representation ℂ G V) (S S' : LocalCorrespondence level)
    (e : S.representatives ≃ S'.representatives) (he : ∀ s, s.val⁻¹ * (e s).val ∈ level) :
    cohomologyAction rho S = cohomologyAction rho S' := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  change cohomologyAction rho S (classOf level rho C) = cohomologyAction rho S' (classOf level rho C)
  rw [cohomologyAction_classOf, cohomologyAction_classOf]
  congr 1
  apply Subtype.ext
  change cochainAction rho S 2 C.val = cochainAction rho S' 2 C.val
  rw [cochainAction_eq_of_equiv rho S S' e he]

/-- A cardinality-matching injection into the other representatives, inside the same cosets. -/
theorem cohomologyAction_eq_of_injective (rho : Representation ℂ G V) (S S' : LocalCorrespondence level)
    (f : S.representatives → S'.representatives) (hf : ∀ s, s.val⁻¹ * (f s).val ∈ level)
    (hcard : S'.representatives.card ≤ S.representatives.card) :
    cohomologyAction rho S = cohomologyAction rho S' := by
  have hinj : Function.Injective f := by
    intro s s' h
    apply Subtype.ext
    apply S.disjoint s.val s.property s'.val s'.property
    have := level.mul_mem (hf s) (level.inv_mem (hf s'))
    rw [h] at this
    convert this using 1
    group
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, le_antisymm (Fintype.card_le_of_injective f hinj) ?_⟩
    simpa only [Fintype.card_coe] using hcard
  exact cohomologyAction_eq_of_equiv rho S S' (Equiv.ofBijective f hbij) hf

end Generic

/-! ### The number of representatives of `T_p` -/

open TernaryPeriodPolynomials.HeckeEigen.Satake in
theorem card_representatives {p : ℕ} (hp : p.Prime) (t : HeckeCorrespondence) (ht : AwayThree t)
    (hg : t.g = gP hp) : t.representatives.card = p ^ 2 + p + 1 := by
  classical
  choose vP BP sP γP hsP hP using plane_iwasawa_pos
  have hcount := prime_plane_count hp t ht hg vP BP sP γP (fun r _ => hP r) (fun r _ => hsP r)
  have hcount1 := prime_plane_count_one hp t ht hg vP BP sP γP (fun r _ => hP r)
    (fun r _ => hsP r)
  rw [← Finset.card_filter_add_card_filter_not (fun r => (sP r : ℚ) = p), hcount, hcount1]
  ring

/-! ### The explicit representatives lie in the double coset -/

open TernaryPeriodPolynomials.HeckeEigen.Satake TernaryPeriodPolynomials.HeckeCommutativity
open PlaneCoordinates LevelOneCosets IdentityPlaneCosets

/-- An element of the level from an explicit integral matrix. -/
def lvl (M : Matrix (Fin 3) (Fin 3) ℤ) (hdet : IsUnit M.det)
    (hrow : ∀ j, ((M 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0) : rationalLevel :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (M.map (Int.cast : ℤ → ℚ)) (by
      rw [show (M.map (Int.cast : ℤ → ℚ)).det = ((M.det : ℤ) : ℚ) from
        (RingHom.map_det (Int.castRingHom ℚ) M).symm]
      exact_mod_cast hdet.ne_zero),
    mem_rationalLevel_of_int _ M rfl hdet hrow⟩

theorem lvl_val (M : Matrix (Fin 3) (Fin 3) ℤ) (hdet : IsUnit M.det)
    (hrow : ∀ j, ((M 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0) :
    (lvl M hdet hrow).val.val = M.map (Int.cast : ℤ → ℚ) := rfl

variable (p : Nat.Primes)

/-- The sign `εp / p`. -/
def sgnP : ℤ := if (p.val : ℤ) % 3 = 1 then 1 else -1

theorem sgnP_mul : (p.val : ℤ) * sgnP p = epsP p := by
  unfold sgnP epsP
  split_ifs <;> ring

theorem isUnit_sgnP : IsUnit (sgnP p) := by
  unfold sgnP
  split_ifs
  · exact isUnit_one
  · exact isUnit_one.neg

/-- `β = (1 - εp)/3`. -/
def betaP : ℤ := (1 - epsP p) / 3

theorem three_betaP (hp3 : p.val ≠ 3) : 3 * betaP p = 1 - epsP p := by
  have h := epsP_mod p hp3
  unfold betaP
  omega

theorem zmod_one {c : ℤ} (hc : c % 3 = 1) : ((c : ℤ) : ZMod 3) = 1 := by
  rw [← ZMod.intCast_mod c 3]
  rw [show c % ((3 : ℕ) : ℤ) = 1 from hc]
  rfl

theorem zmod_three : ((3 : ℤ) : ZMod 3) = 0 := rfl

theorem zmod_neg_three : ((-3 : ℤ) : ZMod 3) = 0 := rfl

theorem sigma_double (hp3 : p.val ≠ 3) :
    ∃ a b : rationalLevel, sExpl p none = a.val * gP p.property * b.val := by
  have R1 := sgnP_mul p
  have R2 := three_betaP p hp3
  have hmod := epsP_mod p hp3
  let Ma : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, -betaP p; 0, 1, 0; 3, 0, epsP p]
  let Mb : Matrix (Fin 3) (Fin 3) ℤ := !![sgnP p, 0, betaP p * sgnP p; 0, 1, 0; -3, 0, epsP p]
  have hda : IsUnit Ma.det := by
    have : Ma.det = 1 := by
      simp only [Ma, Matrix.det_fin_three]
      simp
      linear_combination R2
    rw [this]; exact isUnit_one
  have hdb : IsUnit Mb.det := by
    have : Mb.det = sgnP p := by
      simp only [Mb, Matrix.det_fin_three]
      simp
      linear_combination sgnP p * R2
    rw [this]; exact isUnit_sgnP p
  have hra : ∀ j, ((Ma 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j; fin_cases j
    · exact zmod_three
    · simp [Ma]
    · simpa [Ma] using zmod_one hmod
  have hrb : ∀ j, ((Mb 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j; fin_cases j
    · exact zmod_neg_three
    · simp [Mb]
    · simpa [Mb] using zmod_one hmod
  refine ⟨lvl Ma hda hra, lvl Mb hdb hrb, ?_⟩
  have R1q : (p.val : ℚ) * (sgnP p : ℚ) = (epsP p : ℚ) := by exact_mod_cast R1
  have R2q : 3 * (betaP p : ℚ) = 1 - (epsP p : ℚ) := by exact_mod_cast R2
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, lvl_val, lvl_val, gP_val, sExpl, P_val]
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [Ma, Mb, Matrix.mul_apply, Fin.sum_univ_three, epsU_val] <;>
    first
    | linear_combination R1q + R2q
    | linear_combination (betaP p : ℚ) * R1q
    | linear_combination 3 * R1q
    | linear_combination 3 * (betaP p : ℚ) * R1q + (epsP p : ℚ) * R2q
    | linear_combination -R1q - R2q
    | linear_combination -(betaP p : ℚ) * R1q
    | linear_combination -3 * R1q
    | linear_combination -3 * (betaP p : ℚ) * R1q - (epsP p : ℚ) * R2q

theorem some_none_double (r : Fin p.val) :
    ∃ a b : rationalLevel, sExpl p (some (none, r)) = a.val * gP p.property * b.val := by
  let Ma : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 0; 1, 0, r.val; 0, 0, 1]
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
  rw [Units.val_mul, Units.val_mul, lvl_val, lvl_val, gP_val, sExpl, P_val]
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [Ma, Mb, Matrix.mul_apply, Fin.sum_univ_three, BGL_val, Bmat, icast, wint]

theorem some_some_double (i r : Fin p.val) :
    ∃ a b : rationalLevel, sExpl p (some (some i, r)) = a.val * gP p.property * b.val := by
  let Ma : Matrix (Fin 3) (Fin 3) ℤ := !![1, -(i.val : ℤ), r.val; 0, 1, 0; 0, 0, 1]
  have hda : IsUnit Ma.det := by
    have : Ma.det = 1 := by simp [Ma, Matrix.det_fin_three]
    rw [this]; exact isUnit_one
  have hra : ∀ j, ((Ma 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j; fin_cases j <;> simp [Ma]
  refine ⟨lvl Ma hda hra, 1, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, lvl_val, gP_val, sExpl, P_val]
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [Ma, Matrix.mul_apply, Fin.sum_univ_three, BGL_val, Bmat, icast, wint]

/-- **Every explicit representative lies in `Γ diag(p,1,1) Γ`.** -/
theorem sExpl_double (hp3 : p.val ≠ 3) (i : SIdx p) :
    ∃ a b : rationalLevel, sExpl p i = a.val * gP p.property * b.val := by
  rcases i with _ | ⟨_ | j, r⟩
  · exact sigma_double p hp3
  · exact some_none_double p r
  · exact some_some_double p j r

/-! ### `localOp` at the identity plane -/

theorem P_fixes (x : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) :
    P x B d ∈ MulAction.stabilizer RationalGL3 (QuotientGroup.mk 1 : Flags .plane) := by
  rw [MulAction.mem_stabilizer_iff]
  change (QuotientGroup.mk (P x B d * 1) : Flags .plane) = QuotientGroup.mk 1
  rw [QuotientGroup.eq, mul_one, mul_one]
  apply (parabolic .plane).inv_mem
  change InPlaneParabolic (P x B d)
  constructor <;> simp [P_val]

theorem sExpl_fixes (i : SIdx p) :
    sExpl p i ∈ MulAction.stabilizer RationalGL3 (QuotientGroup.mk 1 : Flags .plane) := by
  rcases i with _ | ⟨j, r⟩ <;> exact P_fixes _ _ _

open CuspOrbits CuspReduction IdentityPlaneCoordinate IdentityPlaneHecke

/-- **`localOp` of `T_p` at the identity plane is the explicit local operator.** -/
theorem localOp_identityPlane (n : ℕ) (t : HeckeCorrespondence) (ht : AwayThree t)
    (hg : t.g = gP p.property) (hp3 : p.val ≠ 3) :
    localOp n trivialCharacter t ht .plane false = cohomologyAction (ρn n) (identityPlaneCosets p) := by
  classical
  have htr := transports_cuspFlag t ht .plane false
  have hex : ∀ s : (identityPlaneCosets p).representatives,
      ∃ s' ∈ (HeckeShapiro.localCorrespondence htr).representatives, s.val⁻¹ * s' ∈ Λ₀ := by
    rintro ⟨s, hs⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨a, b, hab⟩ := sExpl_double p hp3 i
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
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (sExpl_fixes p i))
          (HeckeShapiro.shifted_smul htr hr)
  choose f hfmem hf using hex
  have hcard : (HeckeShapiro.localCorrespondence htr).representatives.card ≤
      (identityPlaneCosets p).representatives.card := by
    rw [HeckeShapiro.localCorrespondence_representatives]
    refine (Finset.card_image_le).trans ?_
    rw [card_representatives p.property t ht hg]
    change _ ≤ (Finset.univ.image (sExpl p)).card
    rw [Finset.card_image_of_injective _ (sExpl_injective p), Finset.card_univ, Fintype.card_option,
      Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    apply le_of_eq
    ring
  unfold localOp
  exact (cohomologyAction_eq_of_injective (ρn n) (identityPlaneCosets p)
    (HeckeShapiro.localCorrespondence htr) (fun s => ⟨f s, hfmem s⟩) hf hcard).symm

/-- **The local `T_p` at the identity-plane cusp, on the binary edge.** For every away-from-three
correspondence `t` of `Γ diag(p,1,1) Γ` (`p ≠ 3`) and odd `n > 0`,
`E(localOp t x) = E(x) + p^{-(n+2)} T_p E(x)`, with `E` the injective binary edge
`H²(Γ_F, Sym^n ⊗ det⁻¹) → H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` and `T_p` the cohomological Hecke operator. -/
theorem edgeH2_localOp (n : ℕ) (hn : 0 < n) (hodd : Odd n) (t : HeckeCorrespondence)
    (ht : AwayThree t) (hg : t.g = gP p.property) (hp3 : p.val ≠ 3)
    (x : CuspH2 n trivialCharacter .plane false) :
    edgeH2 n hn hodd (localOp n trivialCharacter t ht .plane false x) =
      edgeH2 n hn hodd x + ((p.val : ℂ) ^ (n + 2))⁻¹ •
        LevelOneHeckeH1.arithmeticHecke (n + 1) (-1) p (edgeH2 n hn hodd x) := by
  rw [localOp_identityPlane p n t ht hg hp3]
  exact edgeH2_hecke n p hn hodd x

/-- The same identity for the `T_p` correspondence `TpExistence.tp p`, which exists for `p ≠ 3`. -/
theorem edgeH2_localOp_tp (n : ℕ) (hn : 0 < n) (hodd : Odd n) (hp3 : p.val ≠ 3)
    (x : CuspH2 n trivialCharacter .plane false) :
    edgeH2 n hn hodd (localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
        .plane false x) =
      edgeH2 n hn hodd x + ((p.val : ℂ) ^ (n + 2))⁻¹ •
        LevelOneHeckeH1.arithmeticHecke (n + 1) (-1) p (edgeH2 n hn hodd x) :=
  edgeH2_localOp p n hn hodd _ _ (TpExistence.tp_g p) hp3 x

end TernaryPeriodPolynomials.Spectral.IdentityPlaneLocalOp
