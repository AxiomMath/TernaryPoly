module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneDouble
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneLocalOp

@[expose] public section


/-!
# `localOp` of `T_p` at the good-plane cusp

For every away-from-three Hecke correspondence `t` of the double coset `Γ diag(p, 1, 1) Γ`, the
local correspondence of `t` at the good-plane cusp (`HeckeShapiro.localCorrespondence`) has the same
cosets as the conjugate `gF · s · gF⁻¹` of the explicit representatives `s` of `GoodPlaneCosets`
(`conjCosets`): every conjugated representative lies in the double coset (`GoodPlaneDouble`) and
both sets have `p² + p + 1` elements. Hence `localOp t` is the conjugate of the explicit local
operator of the stabilizer `ΛG`, and the edge map `goodPlaneEdge` intertwines it with
`1 + p^{-(n+2)} T_p^{Γ₁'(3)}` (`goodPlaneEdge_localOp`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneLocalOp

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspLevel CuspH2 localOp)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (transports_cuspFlag)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneCosetData (sExpl SIdx)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
  (psiG hH_conj hH'_conj goodPlaneEdge goodPlaneEdgeH2)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneCosets (goodPlaneCosets)

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-! ### The conjugated correspondence -/

/-- The explicit correspondence of `ΛG`, conjugated by the frame into the cusp stabilizer. -/
def conjCosets : LocalHecke.LocalCorrespondence (cuspLevel .plane true) where
  representatives := (goodPlaneCosets p hp3).representatives.image (fun s => gF * s * gF⁻¹)
  stable := by
    intro g hg s hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨t', ht', hmem⟩ := (goodPlaneCosets p hp3).stable _ (hH'_conj g hg) s' hs'
    refine ⟨gF * t' * gF⁻¹, Finset.mem_image_of_mem _ ht', ?_⟩
    have e : (gF * t' * gF⁻¹)⁻¹ * (g * (gF * s' * gF⁻¹)) =
        gF * (t'⁻¹ * ((gF⁻¹ * g * gF⁻¹⁻¹) * s')) * gF⁻¹ := by group
    show (gF * t' * gF⁻¹)⁻¹ * (g * (gF * s' * gF⁻¹)) ∈ cuspLevel .plane true
    rw [e]
    exact hH_conj _ hmem
  disjoint := by
    intro s hs s' hs' h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs'
    have e : gF⁻¹ * ((gF * a * gF⁻¹)⁻¹ * (gF * b * gF⁻¹)) * gF⁻¹⁻¹ = a⁻¹ * b := by group
    have h1 : (gF * a * gF⁻¹)⁻¹ * (gF * b * gF⁻¹) ∈ cuspLevel .plane true := h
    have h2 := hH'_conj _ h1
    rw [e] at h2
    show gF * a * gF⁻¹ = gF * b * gF⁻¹
    rw [(goodPlaneCosets p hp3).disjoint a ha b hb h2]

theorem conj_injective : Function.Injective (fun s : RationalGL3 => gF * s * gF⁻¹) := by
  intro a b h
  have h' : gF * a * gF⁻¹ = gF * b * gF⁻¹ := h
  exact mul_left_cancel (mul_right_cancel h')

theorem card_conjCosets : (conjCosets p hp3).representatives.card = p.val ^ 2 + p.val + 1 := by
  change ((goodPlaneCosets p hp3).representatives.image (fun s => gF * s * gF⁻¹)).card = _
  rw [Finset.card_image_of_injective _ (conj_injective)]
  change (Finset.univ.image (sExpl p)).card = _
  rw [Finset.card_image_of_injective _ (GoodPlaneCosets.sExpl_injective p hp3), Finset.card_univ,
    Fintype.card_option, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
  ring

/-! ### The conjugated representatives fix the cusp flag -/

theorem conj_mem_stabilizer {s : RationalGL3} (hs : s ∈ planeParabolic ℚ) :
    gF * s * gF⁻¹ ∈ MulAction.stabilizer RationalGL3 (CuspOrbits.cuspFlag .plane true) := by
  rw [MulAction.mem_stabilizer_iff, GoodPlaneFrame.cuspFlag_eq]
  change (QuotientGroup.mk (gF * s * gF⁻¹ * gF) : Flags .plane) = QuotientGroup.mk gF
  rw [inv_mul_cancel_right, QuotientGroup.eq]
  have h := (parabolic .plane).inv_mem hs
  simpa [mul_assoc] using h

theorem sExpl_parabolic (i : SIdx p) : sExpl p i ∈ planeParabolic ℚ := by
  rcases i with _ | ⟨j, r⟩
  · change InPlaneParabolic (sExpl p none)
    constructor <;> simp [sExpl, PlaneCoordinates.P_val]
  · change InPlaneParabolic (sExpl p (some (j, r)))
    constructor <;> simp [sExpl, PlaneCoordinates.P_val]

/-! ### `localOp` is the conjugated explicit operator -/

open TernaryPeriodPolynomials.HeckeEigen.Satake in
theorem localOp_eq_conjCosets (n : ℕ) (t : HeckeCorrespondence) (ht : AwayThree t)
    (hg : t.g = gP p.property) :
    localOp n trivialCharacter t ht .plane true =
      LocalHecke.cohomologyAction (rationalCoefficientComponent n trivialCharacter)
        (conjCosets p hp3) := by
  classical
  have htr := transports_cuspFlag t ht .plane true
  have hex : ∀ s : (conjCosets p hp3).representatives,
      ∃ s' ∈ (HeckeShapiro.localCorrespondence htr).representatives,
        s.val⁻¹ * s' ∈ cuspLevel .plane true := by
    rintro ⟨s, hs⟩
    obtain ⟨s0, hs0, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs0
    obtain ⟨a, b, hab⟩ := GoodPlaneDouble.sExpl_double p hp3 i
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
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (conj_mem_stabilizer (sExpl_parabolic p i)))
          (HeckeShapiro.shifted_smul htr hr)
  choose f hfmem hf using hex
  have hcard : (HeckeShapiro.localCorrespondence htr).representatives.card ≤
      (conjCosets p hp3).representatives.card := by
    rw [HeckeShapiro.localCorrespondence_representatives]
    refine (Finset.card_image_le).trans ?_
    exact le_of_eq (by
      rw [IdentityPlaneLocalOp.card_representatives p.property t ht hg, card_conjCosets])
  unfold localOp
  exact (IdentityPlaneLocalOp.cohomologyAction_eq_of_injective
    (rationalCoefficientComponent n trivialCharacter) (conjCosets p hp3)
    (HeckeShapiro.localCorrespondence htr) (fun s => ⟨f s, hfmem s⟩) hf hcard).symm

/-! ### Transport to the block coordinates -/

/-- Conjugation maps the explicit representatives to the conjugated ones. -/
def conjMap : (goodPlaneCosets p hp3).representatives → (conjCosets p hp3).representatives :=
  fun s => ⟨gF * s.val * gF⁻¹,
    Finset.mem_image_of_mem (fun s : RationalGL3 => gF * s * gF⁻¹) s.property⟩

theorem conjMap_bijective : Function.Bijective (conjMap p hp3) := by
  refine ⟨fun a b h => ?_, ?_⟩
  · have h' : gF * a.val * gF⁻¹ = gF * b.val * gF⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (conj_injective h')
  · rintro ⟨s, hs⟩
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    exact ⟨⟨s', hs'⟩, rfl⟩

/-- The bijection between the conjugated and the explicit representatives. -/
def conjEquiv : (conjCosets p hp3).representatives ≃ (goodPlaneCosets p hp3).representatives :=
  (Equiv.ofBijective (conjMap p hp3) (conjMap_bijective p hp3)).symm

theorem conjEquiv_spec (s : (conjCosets p hp3).representatives) :
    s.val = gF * (conjEquiv p hp3 s).val * gF⁻¹ := by
  have h := (Equiv.ofBijective (conjMap p hp3) (conjMap_bijective p hp3)).apply_symm_apply s
  exact (congrArg Subtype.val h).symm

/-- **The local operator at the good plane in block coordinates.** -/
theorem psiG_localOp (n : ℕ) (t : HeckeCorrespondence) (ht : AwayThree t)
    (hg : t.g = TernaryPeriodPolynomials.HeckeEigen.Satake.gP p.property)
    (y : CuspH2 n trivialCharacter .plane true) :
    psiG (localOp n trivialCharacter t ht .plane true y) =
      LocalHecke.cohomologyAction (rationalCoefficientComponent n trivialCharacter)
        (goodPlaneCosets p hp3) (psiG y) := by
  rw [localOp_eq_conjCosets p hp3 n t ht hg]
  exact GoodPlaneConj.conjH2_cohomologyAction (rationalCoefficientComponent n trivialCharacter)
    gF (cuspLevel .plane true) ΛG hH_conj (conjCosets p hp3) (goodPlaneCosets p hp3)
    (conjEquiv p hp3) (fun s => by
      have hs := conjEquiv_spec p hp3 s
      have e : (gF⁻¹ * s.val * gF)⁻¹ * (conjEquiv p hp3 s).val = 1 := by
        rw [hs]
        group
      rw [e]
      exact ΛG.one_mem) y

/-- **The edge of the local `T_p` at the good plane**: for every away-from-three correspondence of
`Γ diag(p,1,1) Γ` and `n > 0`,
`E(localOp t x) = E x + p^{-(n+2)} T_p E x`, with `E = goodPlaneEdge` the injective edge into
`H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` and `T_p` D's Hecke operator `levelHecke`. -/
theorem goodPlaneEdge_localOp (n : ℕ) (hn : 0 < n) (t : HeckeCorrespondence) (ht : AwayThree t)
    (hg : t.g = TernaryPeriodPolynomials.HeckeEigen.Satake.gP p.property)
    (x : CuspH2 n trivialCharacter .plane true) :
    goodPlaneEdge hn (localOp n trivialCharacter t ht .plane true x) =
      goodPlaneEdge hn x + ((p.val : ℂ) ^ (n + 2))⁻¹ •
        LevelThreeHeckeH1.levelHecke (n + 1) (-1) p hp3 (goodPlaneEdge hn x) := by
  change goodPlaneEdgeH2 hn (psiG (localOp n trivialCharacter t ht .plane true x)) =
    goodPlaneEdgeH2 hn (psiG x) + ((p.val : ℂ) ^ (n + 2))⁻¹ •
      LevelThreeHeckeH1.levelHecke (n + 1) (-1) p hp3 (goodPlaneEdgeH2 hn (psiG x))
  rw [psiG_localOp p hp3 n t ht hg]
  exact GoodPlaneHecke.goodPlaneEdgeH2_hecke p hp3 hn (psiG x)

/-- The same for the correspondence `TpExistence.tp p`. -/
theorem goodPlaneEdge_localOp_tp (n : ℕ) (hn : 0 < n) (x : CuspH2 n trivialCharacter .plane true) :
    goodPlaneEdge hn (localOp n trivialCharacter (TpExistence.tp p)
        (TpExistence.tp_awayThree p hp3) .plane true x) =
      goodPlaneEdge hn x + ((p.val : ℂ) ^ (n + 2))⁻¹ •
        LevelThreeHeckeH1.levelHecke (n + 1) (-1) p hp3 (goodPlaneEdge hn x) :=
  goodPlaneEdge_localOp p hp3 n hn _ _ (TpExistence.tp_g p) x

end TernaryPeriodPolynomials.LevelThree.GoodPlaneLocalOp
