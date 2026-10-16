module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneCosetsBasic
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.AmbientHecke

@[expose] public section


/-!
# The local `T_p`-cosets at the good plane

For a prime `p ≠ 3` the `1 + p(p+1)` elements `σ₀ = P(0, 1, εp)` and
`s_{j,r} = P(w_{j,r}, B_j, 1)` (`GoodPlaneCosetData.sExpl`) form a local correspondence of the
good-plane stabilizer `ΛG = {P(b, κ(m), d) : b ∈ ℤ², m ∈ Γ₁'(3), d = ±1}` (`goodPlaneCosets`): the
cosets `sΛG` are pairwise distinct (`sExpl_disjoint`) and permuted by left multiplication by `ΛG`.
Stability is proved for the elements `P(b, κ(m), 1)` using the Levi transitions of
`GoodPlaneCosetsBasic` and the index `prevIdx` (`stab_PK`), for `diag(1, 1, -1)` separately
(`stab_neg`), and extended to the whole group by `Stab_mul`. The final section computes the
transitions of the explicit representatives under `u(b) diag(κ(m), 1)` (`next_none`, `next_some`,
`delta_none`, `delta_some`), exactly as in `IdentityPlaneCosets`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneCosets

open TernaryPeriodPolynomials.Spectral
open PlaneCoordinates
open LevelOneCosets (integralEmbed integralEmbed_val det_units)
open IdentityPlaneCosets (icast icast_zero icast_add icast_sub icast_neg icast_injective imul
  bmul_zero IsInt epsP epsU epsU_val epsU_ne_one epsP_natAbs)
open GoodPlaneCosetData GoodPlaneFrame GoodPlaneModel
open LevelThreeCosets (signP levelNext levelDelta levelCosets)
open AmbientHecke (nextRep nextRep_unique deltaRep deltaRep_val)

variable (p : Nat.Primes)

/-! ### Membership in `ΛG` in coordinates -/

theorem P_mem_ΛG {x : ℚ × ℚ} {B : GL (Fin 2) ℚ} {d : ℚˣ} (hd : d = 1) (hx : IsInt x)
    (hB : ∃ μ : binaryArithmeticLevel, B = Em μ) : P x B d ∈ ΛG := by
  obtain ⟨b, rfl⟩ := hx
  obtain ⟨μ, rfl⟩ := hB
  subst hd
  exact PK_mem b μ

/-- **Membership in `ΛG` in coordinates.** -/
theorem P_mem_ΛG_iff (x : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) :
    P x B d ∈ ΛG ↔
      (∃ d' : ℤˣ, d = uq d') ∧ IsInt x ∧ ∃ μ : binaryArithmeticLevel, B = Em μ := by
  rw [mem_ΛG_iff]
  constructor
  · rintro ⟨b, m, d', h⟩
    obtain ⟨h1, h2, h3⟩ := P_injective h
    exact ⟨⟨d', h3⟩, ⟨b, h1⟩, ⟨m, h2⟩⟩
  · rintro ⟨⟨d', rfl⟩, ⟨b, rfl⟩, ⟨m, rfl⟩⟩
    exact ⟨b, m, d', rfl⟩

/-! ### The signs `ε`, `uq d` -/

theorem epsU_ne_uq (d : ℤˣ) : epsU p ≠ uq d := by
  intro h
  have h1 : (epsP p : ℚ) = ((d : ℤ) : ℚ) := congrArg (fun u : ℚˣ => (u : ℚ)) h
  have h2 : epsP p = (d : ℤ) := by exact_mod_cast h1
  have h3 : (epsP p).natAbs = p.val := epsP_natAbs p
  have h4 := p.property.two_le
  rcases Int.isUnit_iff.mp d.isUnit with e | e <;> rw [h2, e] at h3 <;> simp at h3 <;> omega

theorem epsU_inv_ne_uq (d : ℤˣ) : (epsU p)⁻¹ ≠ uq d := by
  intro h
  apply epsU_ne_uq p d⁻¹
  have e : uq d⁻¹ = (uq d)⁻¹ := map_inv (Units.map (Int.castRingHom ℚ : ℤ →* ℚ)) d
  rw [e]
  exact inv_eq_iff_eq_inv.mp h

/-! ### Injectivity of the explicit representatives -/

theorem sExpl_injective (hp3 : p.val ≠ 3) : Function.Injective (sExpl p) := by
  intro i i' h
  cases i with
  | none =>
    cases i' with
    | none => rfl
    | some jr =>
      obtain ⟨_j, _r⟩ := jr
      obtain ⟨-, -, hd⟩ := P_injective h
      exact absurd hd (epsU_ne_one p)
  | some jr =>
    obtain ⟨j, r⟩ := jr
    cases i' with
    | none =>
      obtain ⟨-, -, hd⟩ := P_injective h
      exact absurd hd.symm (epsU_ne_one p)
    | some jr' =>
      obtain ⟨_j', r'⟩ := jr'
      obtain ⟨hw, hB, -⟩ := P_injective h
      have hj := BG_injective p hp3 hB
      subst hj
      have hr : r = r' := by
        apply rep_unique p j
        rw [icast_sub, hw, sub_self, bmul_zero]
        exact ⟨0, rfl⟩
      rw [hr]

/-- **Disjointness** of the explicit cosets. -/
theorem sExpl_disjoint (hp3 : p.val ≠ 3) (i i' : SIdx p)
    (h : (sExpl p i)⁻¹ * sExpl p i' ∈ ΛG) : i = i' := by
  cases i with
  | none =>
    cases i' with
    | none => rfl
    | some jr =>
      exfalso
      obtain ⟨_j, _r⟩ := jr
      simp only [sExpl] at h
      rw [P_inv, P_mul, P_mem_ΛG_iff] at h
      obtain ⟨⟨d', hd'⟩, -, -⟩ := h
      rw [mul_one] at hd'
      exact epsU_inv_ne_uq p d' hd'
  | some jr =>
    obtain ⟨j, r⟩ := jr
    cases i' with
    | none =>
      exfalso
      simp only [sExpl] at h
      rw [P_inv, P_mul, P_mem_ΛG_iff] at h
      obtain ⟨⟨d', hd'⟩, -, -⟩ := h
      rw [inv_one, one_mul] at hd'
      exact epsU_ne_uq p d' hd'
    | some jr' =>
      obtain ⟨_j', r'⟩ := jr'
      simp only [sExpl] at h
      rw [P_inv, P_mul, P_mem_ΛG_iff] at h
      obtain ⟨-, hx, ⟨μ, hμ⟩⟩ := h
      have hj := BG_unique p hp3 hμ
      subst hj
      have hr : r' = r := by
        apply rep_unique p j
        rw [icast_sub, bmul_sub]
        obtain ⟨c, hc⟩ := hx
        refine ⟨c, ?_⟩
        rw [← hc]
        simp only [Units.val_one, neg_smul, one_smul, inv_one]
        abel
      rw [hr]

/-! ### Stability -/

/-- The previous index: `next m (prevIdx m j) = j`. -/
def prevIdx (hp3 : p.val ≠ 3) (m : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    Option (Fin p.val) :=
  ((levelCosets p hp3).nextEquiv m).symm j

theorem next_prevIdx (hp3 : p.val ≠ 3) (m : binaryArithmeticLevel) (j : Option (Fin p.val)) :
    levelNext p hp3 m (prevIdx p hp3 m j) = j :=
  ((levelCosets p hp3).nextEquiv m).apply_symm_apply j

/-- `g` permutes the explicit cosets: for every `s` there is `t` with `t⁻¹ g s ∈ ΛG`. -/
def Stab (g : RationalGL3) : Prop :=
  ∀ i : SIdx p, ∃ i' : SIdx p, (sExpl p i')⁻¹ * (g * sExpl p i) ∈ ΛG

theorem Stab_mul {g g' : RationalGL3} (hg : Stab p g) (hg' : Stab p g') : Stab p (g * g') := by
  intro i
  obtain ⟨i1, h1⟩ := hg' i
  obtain ⟨i2, h2⟩ := hg i1
  refine ⟨i2, ?_⟩
  have e : (sExpl p i2)⁻¹ * (g * g' * sExpl p i) =
      ((sExpl p i2)⁻¹ * (g * sExpl p i1)) * ((sExpl p i1)⁻¹ * (g' * sExpl p i)) := by
    group
  rw [e]
  exact ΛG.mul_mem h2 h1

/-- Conjugation of `PK b m` by `σ₀`: `σ₀⁻¹ u(b) κ(m) σ₀ = u(εp b) κ(m)`. -/
theorem sigma_conj (b : ℤ × ℤ) (m : binaryArithmeticLevel) :
    (sExpl p none)⁻¹ * (PK b m * sExpl p none) = PK (epsP p • b) m := by
  simp only [sExpl, PK]
  rw [P_inv, P_mul, P_mul]
  congr 1
  · simp [bmul_zero, bmul_one, icast, epsU_val]
  · simp
  · simp

/-- **Stability under `u(b) κ(m)`.** -/
theorem stab_PK (hp3 : p.val ≠ 3) (b : ℤ × ℤ) (m : binaryArithmeticLevel) : Stab p (PK b m) := by
  intro i
  cases i with
  | none =>
    refine ⟨none, ?_⟩
    rw [sigma_conj]
    exact PK_mem _ _
  | some jr =>
    obtain ⟨j, r⟩ := jr
    refine ⟨some (prevIdx p hp3 m j,
      repIdx p (prevIdx p hp3 m j) (b + imul (kap m).val (wint p j r))), ?_⟩
    simp only [sExpl, PK]
    rw [P_inv, P_mul, P_mul]
    apply P_mem_ΛG
    · simp
    · have h := rep_spec p (prevIdx p hp3 m j) (b + imul (kap m).val (wint p j r))
      refine ⟨quotVec p (prevIdx p hp3 m j) (b + imul (kap m).val (wint p j r)), ?_⟩
      simp only [inv_one, Units.val_one, one_smul, neg_smul]
      change _ = icast _
      rw [← h, icast_sub, icast_add, bmul_sub, icast_imul_kap]
      simp only [bmul_add]
      abel
    · refine ⟨levelDelta p hp3 m (prevIdx p hp3 m j), ?_⟩
      have h := levi_transition p hp3 m (prevIdx p hp3 m j)
      rw [next_prevIdx] at h
      rw [← mul_assoc, h, mul_assoc, inv_mul_cancel, mul_one]

theorem Pg_neg_one : Pg 0 1 (-1) = P 0 1 (uq (-1)) := by
  simp [Pg]

theorem Pg_neg_comm_sigma :
    Pg 0 1 (-1) * sExpl p none = sExpl p none * Pg 0 1 (-1) := by
  rw [Pg_neg_one]
  simp only [sExpl]
  rw [P_mul, P_mul]
  congr 1 <;> first | exact mul_comm _ _ | simp [bmul_zero]

/-- Conjugation of `P(w, B, 1)` by `diag(1, 1, -1)` and `P(w', B, 1)`. -/
theorem neg_conj (B : GL (Fin 2) ℚ) (w w' : ℚ × ℚ) :
    (P w' B 1)⁻¹ * (P 0 1 (uq (-1)) * P w B 1) =
      P (-bmul (B⁻¹ : GL (Fin 2) ℚ).val (w' + w)) 1 (uq (-1)) := by
  have hu : (((uq (-1))⁻¹ : ℚˣ) : ℚ) = -1 := by
    rw [uq_inv]
    simp
  rw [P_inv, P_mul, P_mul]
  congr 1
  · rw [hu]
    simp only [inv_one, Units.val_one, neg_smul, one_smul, zero_add, bmul_one, bmul_neg,
      bmul_add]
    abel
  · simp
  · simp

/-- **Stability under `diag(1, 1, -1)`.** -/
theorem stab_neg : Stab p (Pg 0 1 (-1)) := by
  intro i
  cases i with
  | none =>
    refine ⟨none, ?_⟩
    rw [Pg_neg_comm_sigma, inv_mul_cancel_left]
    exact Pg_mem 0 1 (-1)
  | some jr =>
    obtain ⟨j, r⟩ := jr
    refine ⟨some (j, repIdx p j (-(wint p j r))), ?_⟩
    have h := rep_spec p j (-(wint p j r))
    have hq : icast (quotVec p j (-(wint p j r))) =
        -bmul ((BG p j)⁻¹ : GL (Fin 2) ℚ).val
          (icast (wint p j (repIdx p j (-(wint p j r)))) + icast (wint p j r)) := by
      rw [← h, icast_sub, icast_neg, ← bmul_neg]
      congr 1
      abel
    have e : Pg (quotVec p j (-(wint p j r))) 1 (-1) =
        P (icast (quotVec p j (-(wint p j r)))) 1 (uq (-1)) := by
      simp [Pg]
    rw [Pg_neg_one]
    simp only [sExpl]
    rw [neg_conj, ← hq, ← e]
    exact Pg_mem _ _ _

theorem Pg_split (b : ℤ × ℤ) (m : binaryArithmeticLevel) (d : ℤˣ) :
    Pg b m d = PK b m * Pg 0 1 d := by
  have h0 : act m 1 0 = 0 := by simp [act, imul]
  rw [PK_eq_Pg, Pg_mul, h0, add_zero, mul_one, one_mul]

/-- **Stability under every element of `ΛG`.** -/
theorem stab_Pg (hp3 : p.val ≠ 3) (b : ℤ × ℤ) (m : binaryArithmeticLevel) (d : ℤˣ) :
    Stab p (Pg b m d) := by
  rcases Int.units_eq_one_or d with rfl | rfl
  · rw [← PK_eq_Pg]
    exact stab_PK p hp3 b m
  · rw [Pg_split]
    exact Stab_mul p (stab_PK p hp3 b m) (stab_neg p)

theorem sExpl_stable (hp3 : p.val ≠ 3) (g : RationalGL3) (hg : g ∈ ΛG) (i : SIdx p) :
    ∃ i' : SIdx p, (sExpl p i')⁻¹ * (g * sExpl p i) ∈ ΛG := by
  obtain ⟨b, m, d, rfl⟩ := (mem_ΛG_iff g).mp hg
  exact stab_Pg p hp3 b m d i

/-! ### The explicit local correspondence -/

/-- **The explicit local correspondence at the good plane.** -/
def goodPlaneCosets (hp3 : p.val ≠ 3) : LocalHecke.LocalCorrespondence ΛG where
  representatives := Finset.univ.image (sExpl p)
  stable := by
    intro g hg s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨i', hi'⟩ := sExpl_stable p hp3 g hg i
    exact ⟨sExpl p i', Finset.mem_image_of_mem _ (Finset.mem_univ _), hi'⟩
  disjoint := by
    intro s hs s' hs' h
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp hs'
    rw [sExpl_disjoint p hp3 i i' h]

theorem sExpl_mem (hp3 : p.val ≠ 3) (i : SIdx p) :
    sExpl p i ∈ (goodPlaneCosets p hp3).representatives :=
  Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem det_integralEmbed (g : GL (Fin 2) ℤ) :
    ((integralEmbed g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (((g : Matrix (Fin 2) (Fin 2) ℤ).det : ℤ) : ℚ) := by
  rw [integralEmbed_val]
  exact (RingHom.map_det (Int.castRingHom ℚ) (g : Matrix (Fin 2) (Fin 2) ℤ)).symm

/-- No explicit representative lies in `ΛG`. -/
theorem sExpl_not_mem (i : SIdx p) : sExpl p i ∉ ΛG := by
  intro h
  cases i with
  | none =>
    simp only [sExpl] at h
    obtain ⟨⟨d', hd'⟩, -, -⟩ := (P_mem_ΛG_iff _ _ _).mp h
    exact epsU_ne_uq p d' hd'
  | some jr =>
    obtain ⟨_j, _r⟩ := jr
    simp only [sExpl] at h
    obtain ⟨-, -, ⟨μ, hμ⟩⟩ := (P_mem_ΛG_iff _ _ _).mp h
    have hdet := congrArg (fun g : GL (Fin 2) ℚ => (g : Matrix (Fin 2) (Fin 2) ℚ).det) hμ
    simp only [BG_val, Bmat_det] at hdet
    rw [Em_apply, det_integralEmbed] at hdet
    have h2 : (p.val : ℚ) ≥ 2 := by exact_mod_cast p.property.two_le
    rcases det_units (kap μ) with h1 | h1 <;> rw [h1] at hdet <;> push_cast at hdet <;> linarith

/-! ### Explicit transitions -/

/-- The representative with index `i`. -/
def toRep (hp3 : p.val ≠ 3) (i : SIdx p) : (goodPlaneCosets p hp3).representatives :=
  ⟨sExpl p i, sExpl_mem p hp3 i⟩

theorem toRep_val (hp3 : p.val ≠ 3) (i : SIdx p) : (toRep p hp3 i).val = sExpl p i := rfl

/-- Transition of `σ₀` under any element `u(b) κ(m)`. -/
theorem next_none (hp3 : p.val ≠ 3) (b : ℤ × ℤ) (m : binaryArithmeticLevel) :
    nextRep (goodPlaneCosets p hp3) (MK b m) (toRep p hp3 none) = toRep p hp3 none := by
  apply nextRep_unique
  change (sExpl p none)⁻¹ * PK b m * sExpl p none ∈ ΛG
  rw [mul_assoc, sigma_conj]
  exact PK_mem _ _

theorem delta_none (hp3 : p.val ≠ 3) (b : ℤ × ℤ) (m : binaryArithmeticLevel) :
    deltaRep (goodPlaneCosets p hp3) (MK b m) (toRep p hp3 none) = MK (epsP p • b) m := by
  apply Subtype.ext
  rw [deltaRep_val, next_none]
  change (sExpl p none)⁻¹ * PK b m * sExpl p none = PK (epsP p • b) m
  rw [mul_assoc, sigma_conj]

/-- The next index of `(j, r)` under `u(b) κ(m)`. -/
def nextIdx (hp3 : p.val ≠ 3) (b : ℤ × ℤ) (m : binaryArithmeticLevel) (j : Option (Fin p.val))
    (r : Fin p.val) : Option (Fin p.val) × Fin p.val :=
  (levelNext p hp3 m j,
    repIdx p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r - b)))

/-- The radical part `q = B_k⁻¹ (m⁻¹(w - b) - w')` of the transition. -/
def transVec (hp3 : p.val ≠ 3) (b : ℤ × ℤ) (m : binaryArithmeticLevel) (j : Option (Fin p.val))
    (r : Fin p.val) : ℤ × ℤ :=
  quotVec p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r - b))

/-- The transition vector identity `B_j⁻¹ (b - w + κ(m) w') = -κ(δ) q`. -/
theorem trans_vector (hp3 : p.val ≠ 3) (b : ℤ × ℤ) (m : binaryArithmeticLevel)
    (j : Option (Fin p.val)) (r : Fin p.val) :
    -bmul ((BG p j)⁻¹ : GL (Fin 2) ℚ).val (icast (wint p j r)) +
        bmul ((BG p j)⁻¹ : GL (Fin 2) ℚ).val
          (icast b + bmul (Em m).val (icast (wint p (nextIdx p hp3 b m j r).1
            (nextIdx p hp3 b m j r).2))) =
      icast (-imul (kap (levelDelta p hp3 m j)).val (transVec p hp3 b m j r)) := by
  have hrep := rep_spec p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r - b))
  have hx : icast (imul (kap (m⁻¹)).val (wint p j r - b)) =
      bmul ((Em m)⁻¹ : GL (Fin 2) ℚ).val (icast (wint p j r - b)) := (bmul_Em_inv m _).symm
  simp only [nextIdx, transVec]
  set w'' := wint p (levelNext p hp3 m j)
    (repIdx p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r - b)))
  set q := quotVec p (levelNext p hp3 m j) (imul (kap (m⁻¹)).val (wint p j r - b))
  set x := imul (kap (m⁻¹)).val (wint p j r - b)
  rw [icast_sub, bmul_sub] at hrep
  calc -bmul ((BG p j)⁻¹ : GL (Fin 2) ℚ).val (icast (wint p j r)) +
        bmul ((BG p j)⁻¹ : GL (Fin 2) ℚ).val (icast b + bmul (Em m).val (icast w''))
      = bmul ((BG p j)⁻¹ : GL (Fin 2) ℚ).val
          (icast b + bmul (Em m).val (icast w'') - icast (wint p j r)) := by
        rw [bmul_sub]; abel
    _ = bmul (Em (levelDelta p hp3 m j)).val
          (bmul ((BG p (levelNext p hp3 m j))⁻¹ : GL (Fin 2) ℚ).val
            (bmul ((Em m)⁻¹ : GL (Fin 2) ℚ).val
              (icast b + bmul (Em m).val (icast w'') - icast (wint p j r)))) := by
        rw [levi_transition' p hp3 m j, Units.val_mul, Units.val_mul, bmul_mul, bmul_mul]
    _ = bmul (Em (levelDelta p hp3 m j)).val
          (bmul ((BG p (levelNext p hp3 m j))⁻¹ : GL (Fin 2) ℚ).val (icast w'' - icast x)) := by
        congr 2
        rw [hx, bmul_sub, bmul_add, bmul_inv_cancel, icast_sub, bmul_sub]
        abel
    _ = bmul (Em (levelDelta p hp3 m j)).val (-icast q) := by
        rw [bmul_sub, ← hrep, neg_sub]
    _ = icast (-imul (kap (levelDelta p hp3 m j)).val q) := by
        rw [bmul_neg, bmul_Em, icast_neg]

theorem trans_product (hp3 : p.val ≠ 3) (b : ℤ × ℤ) (m : binaryArithmeticLevel)
    (j : Option (Fin p.val)) (r : Fin p.val) :
    (sExpl p (some (j, r)))⁻¹ * PK b m * sExpl p (some (nextIdx p hp3 b m j r)) =
      PK (-imul (kap (levelDelta p hp3 m j)).val (transVec p hp3 b m j r))
        (levelDelta p hp3 m j) := by
  simp only [sExpl, PK]
  rw [P_inv, P_mul, P_mul]
  congr 1
  · simp only [Units.val_one, one_smul, neg_smul, inv_one, mul_one, Units.val_mul, bmul_mul]
    rw [add_assoc, ← bmul_add]
    exact trans_vector p hp3 b m j r
  · rw [mul_assoc]
    exact trans_levi p hp3 m j
  · simp

/-- Transition of `s_{j,r}`. -/
theorem next_some (hp3 : p.val ≠ 3) (b : ℤ × ℤ) (m : binaryArithmeticLevel)
    (j : Option (Fin p.val)) (r : Fin p.val) :
    nextRep (goodPlaneCosets p hp3) (MK b m) (toRep p hp3 (some (j, r))) =
      toRep p hp3 (some (nextIdx p hp3 b m j r)) := by
  apply nextRep_unique
  change (sExpl p (some (j, r)))⁻¹ * PK b m * sExpl p (some (nextIdx p hp3 b m j r)) ∈ ΛG
  rw [trans_product]
  exact PK_mem _ _

theorem delta_some (hp3 : p.val ≠ 3) (b : ℤ × ℤ) (m : binaryArithmeticLevel)
    (j : Option (Fin p.val)) (r : Fin p.val) :
    deltaRep (goodPlaneCosets p hp3) (MK b m) (toRep p hp3 (some (j, r))) =
      MK (-imul (kap (levelDelta p hp3 m j)).val (transVec p hp3 b m j r))
        (levelDelta p hp3 m j) := by
  apply Subtype.ext
  rw [deltaRep_val, next_some]
  exact trans_product p hp3 b m j r

end TernaryPeriodPolynomials.LevelThree.GoodPlaneCosets
