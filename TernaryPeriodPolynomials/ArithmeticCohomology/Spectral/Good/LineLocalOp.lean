module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneLocalOp

@[expose] public section


/-!
# `localOp` of `T_p` at the good-line cusp

The reference good-line cusp `cuspFlag .line true` is a `Γ`-translate `γ⁻¹ F` of the good line
`F = ⟨e₃⟩`. Transport by `γ` (`stabilizerTransportH2`) intertwines the local Hecke operators whose
representatives correspond up to the stabilizer (`transport_cohomologyAction`). For every
away-from-three correspondence `t` of `Γ diag(p,1,1) Γ`, the local correspondence of `t` at the cusp
matches the conjugate of the explicit `goodLineCosets p` (`p + 1 + p²` cosets), so
`ψ ∘ localOp t = T_{explicit} ∘ ψ` (`transport_localOp`), and on the classes with vanishing radical
restriction the binary edge turns `localOp t` into `1 + p^{-(n+1)} T_p` (`edgeK_localOp`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Spectral.GoodLineLocalOp

open LocalHecke

/-! ### Transport of local Hecke operators -/

section Transport

variable {V : Type} [AddCommGroup V] [Module ℂ V] {X : Type} [MulAction RationalGL3 X]
variable (level : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
variable (element : level) (source target : X) (transports : element.val • source = target)

theorem transport_cochainAction (S : LocalCorrespondence (fixedPointLevel level target))
    (S' : LocalCorrespondence (fixedPointLevel level source))
    (e : S.representatives ≃ S'.representatives)
    (he : ∀ s, (element.val⁻¹ * s.val * element.val)⁻¹ * (e s).val ∈ fixedPointLevel level source)
    (f : cochains (fixedPointLevel level source) ρ 2) :
    stabilizerTransportCochain level ρ element source target transports 2 (cochainAction ρ S' 2 f) =
      cochainAction ρ S 2 (stabilizerTransportCochain level ρ element source target transports 2 f) := by
  apply Subtype.ext
  funext x
  change ρ element.val (∑ s' ∈ S'.representatives,
      ρ s' (f.val (fun i => s'⁻¹ * (element.val⁻¹ * x i)))) =
    ∑ s ∈ S.representatives, ρ s (ρ element.val (f.val (fun i => element.val⁻¹ * (s⁻¹ * x i))))
  rw [map_sum, ← Finset.sum_coe_sort S.representatives, ← Finset.sum_coe_sort S'.representatives]
  refine (Fintype.sum_equiv e.symm _ _ (fun s' => ?_))
  set s := e.symm s'
  have hs : e s = s' := e.apply_symm_apply s'
  let l : fixedPointLevel level source := ⟨_, he s⟩
  have hx : (fun i => s'.val⁻¹ * (element.val⁻¹ * x i)) =
      fun i => l⁻¹.val * (element.val⁻¹ * (s.val⁻¹ * x i)) := by
    funext i
    simp only [l, Subgroup.coe_inv, hs]
    group
  rw [hx, f.property l⁻¹ (fun i => element.val⁻¹ * (s.val⁻¹ * x i)), ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  simp only [l, Subgroup.coe_inv, hs]
  group

theorem transport_cohomologyAction (S : LocalCorrespondence (fixedPointLevel level target))
    (S' : LocalCorrespondence (fixedPointLevel level source))
    (e : S.representatives ≃ S'.representatives)
    (he : ∀ s, (element.val⁻¹ * s.val * element.val)⁻¹ * (e s).val ∈ fixedPointLevel level source)
    (y : H2 (fixedPointLevel level source) ρ) :
    stabilizerTransportH2 level ρ element source target transports (cohomologyAction ρ S' y) =
      cohomologyAction ρ S (stabilizerTransportH2 level ρ element source target transports y) := by
  induction y using Submodule.Quotient.induction_on with
  | _ C =>
  change stabilizerTransportH2 level ρ element source target transports
      (cohomologyAction ρ S' (classOf _ ρ C)) =
    cohomologyAction ρ S (stabilizerTransportH2 level ρ element source target transports (classOf _ ρ C))
  rw [cohomologyAction_classOf]
  change classOf _ ρ (stabilizerTransportCycle level ρ element source target transports _) =
    cohomologyAction ρ S (classOf _ ρ (stabilizerTransportCycle level ρ element source target transports C))
  rw [cohomologyAction_classOf]
  congr 1
  apply Subtype.ext
  exact transport_cochainAction level ρ element source target transports S S' e he C.val

/-- Transport back and forth is the identity. -/
theorem transport_inverse (y : H2 (fixedPointLevel level source) ρ) :
    stabilizerTransportH2 level ρ element⁻¹ target source (by rw [← transports]; simp)
        (stabilizerTransportH2 level ρ element source target transports y) = y := by
  induction y using Submodule.Quotient.induction_on with
  | _ C =>
  change classOf _ ρ (stabilizerTransportCycle level ρ element⁻¹ target source _
    (stabilizerTransportCycle level ρ element source target transports C)) = classOf _ ρ C
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change ρ (element⁻¹).val (ρ element.val (C.val.val (fun i => element.val⁻¹ *
    ((element⁻¹).val⁻¹ * x i)))) = C.val.val x
  rw [← Module.End.mul_apply, ← map_mul]
  simp

end Transport

/-! ### The good-line cusp -/

open PlaneCoordinates LevelOneCosets IdentityPlaneCosets LineCoordinates GoodLineCosets GoodLineEdge
open IdentityPlaneCoordinate GoodLineCoordinate GoodLineHecke CuspOrbits CuspReduction IdentityPlaneLocalOp
open TernaryPeriodPolynomials.HeckeEigen.Satake

theorem goodLine_transporter :
    ∃ γ : rationalLevel, γ.val • cuspFlag .line true = (QuotientGroup.mk rationalGoodLine : Flags .line) :=
  cuspFlag_transporter .line true _ (by simp [rationalGoodLine_good])

/-- The chosen transporter from the reference cusp to the good line `⟨e₃⟩`. -/
def gammaL : rationalLevel := goodLine_transporter.choose

theorem gammaL_smul :
    (gammaL).val • cuspFlag .line true = (QuotientGroup.mk rationalGoodLine : Flags .line) :=
  goodLine_transporter.choose_spec

variable (n : ℕ)

/-- **Transport from the good-line cusp to `Λ₁`.** -/
def psiL : CuspH2 n trivialCharacter .line true →ₗ[ℂ] H2 Λ₁ (ρn n) :=
  stabilizerTransportH2 rationalLevel (ρn n) gammaL (cuspFlag .line true)
    (QuotientGroup.mk rationalGoodLine) gammaL_smul

theorem psiL_injective : Function.Injective (psiL n) := by
  intro y y' h
  have e1 := transport_inverse rationalLevel (ρn n) gammaL (cuspFlag .line true)
    (QuotientGroup.mk rationalGoodLine) gammaL_smul y
  have e2 := transport_inverse rationalLevel (ρn n) gammaL (cuspFlag .line true)
    (QuotientGroup.mk rationalGoodLine) gammaL_smul y'
  change stabilizerTransportH2 rationalLevel (ρn n) gammaL (cuspFlag .line true)
    (QuotientGroup.mk rationalGoodLine) gammaL_smul y =
    stabilizerTransportH2 rationalLevel (ρn n) gammaL (cuspFlag .line true)
    (QuotientGroup.mk rationalGoodLine) gammaL_smul y' at h
  rw [← e1, ← e2, h]

theorem Q_fixes (c : ℚ × ℚ) (B : GL (Fin 2) ℚ) (d : ℚˣ) :
    Q c B d ∈ MulAction.stabilizer RationalGL3 (QuotientGroup.mk rationalGoodLine : Flags .line) := by
  rw [MulAction.mem_stabilizer_iff]
  change (QuotientGroup.mk (Q c B d * rationalGoodLine) : Flags .line) = QuotientGroup.mk rationalGoodLine
  rw [QuotientGroup.eq]
  change InLineParabolic ((Q c B d * rationalGoodLine)⁻¹ * rationalGoodLine)
  rw [_root_.mul_inv_rev, rationalGoodLine_inverse, Q_inv]
  constructor <;>
    simp [Units.val_mul, Q_val, rationalGoodLine, Matrix.mul_apply, Fin.sum_univ_three]

variable (p : Nat.Primes)

theorem levi_eq_sExpl (j : Option (Fin p.val)) :
    rExpl p (.inl j) = sExpl p (some (j, ⟨0, p.property.pos⟩)) := by
  have h0 : icast (wint p j ⟨0, p.property.pos⟩) = 0 := by
    cases j <;> simp [wint, icast]
  simp only [rExpl, sExpl]
  rw [h0, ← levi_eq_Q]
  apply Units.ext
  rw [P_val]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [planeLevi, planeBlock]

theorem tau_eq_sExpl (c : Fin p.val × Fin p.val) :
    rExpl p (.inr c) = Qint (cvec p c) 1 * sExpl p none := by
  have hs : sExpl p none = Q 0 1 (epsU p) := by
    simp only [sExpl]
    rw [← levi_eq_Q]
    apply Units.ext
    rw [P_val]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [planeLevi, planeBlock]
  rw [hs, Qint, Q_mul, map_one, inv_one, Units.val_one, vmul_zero, smul_zero, add_zero, mul_one,
    one_mul]
  rfl

/-- **Every explicit good-line representative lies in `Γ diag(p,1,1) Γ`.** -/
theorem rExpl_double (hp3 : p.val ≠ 3) (i : LIdx p) :
    ∃ a b : rationalLevel, rExpl p i = a.val * gP p.property * b.val := by
  rcases i with j | c
  · rw [levi_eq_sExpl]
    exact sExpl_double p hp3 _
  · obtain ⟨a, b, hab⟩ := sExpl_double p hp3 none
    have hmem : Qint (cvec p c) 1 ∈ rationalLevel := (Qint_mem (cvec p c) 1).1
    refine ⟨⟨Qint (cvec p c) 1, hmem⟩ * a, b, ?_⟩
    rw [tau_eq_sExpl, hab]
    simp [mul_assoc]

theorem rExpl_fixes (i : LIdx p) :
    rExpl p i ∈ MulAction.stabilizer RationalGL3 (QuotientGroup.mk rationalGoodLine : Flags .line) := by
  rcases i with j | c <;> exact Q_fixes _ _ _

theorem conj_mem_Λ₁ (l : RationalGL3)
    (hl : l ∈ fixedPointLevel rationalLevel (cuspFlag .line true)) :
    gammaL.val * l * gammaL.val⁻¹ ∈ Λ₁ := by
  refine Subgroup.mem_inf.mpr ⟨rationalLevel.mul_mem (rationalLevel.mul_mem gammaL.2 hl.1)
    (rationalLevel.inv_mem gammaL.2), ?_⟩
  rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, ← gammaL_smul, inv_smul_smul,
    MulAction.mem_stabilizer_iff.mp hl.2]

theorem conj_fixes (g : RationalGL3)
    (hg : g ∈ MulAction.stabilizer RationalGL3 (QuotientGroup.mk rationalGoodLine : Flags .line)) :
    gammaL.val⁻¹ * g * gammaL.val ∈ MulAction.stabilizer RationalGL3 (cuspFlag .line true) := by
  rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, gammaL_smul,
    MulAction.mem_stabilizer_iff.mp hg, ← gammaL_smul, inv_smul_smul]

/-- **Transport of `localOp` of `T_p` at the good-line cusp.** -/
theorem transport_localOp (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP p.property)
    (hp3 : p.val ≠ 3) (y : CuspH2 n trivialCharacter .line true) :
    psiL n (localOp n trivialCharacter t ht .line true y) =
      cohomologyAction (ρn n) (goodLineCosets p) (psiL n y) := by
  classical
  have htr := transports_cuspFlag t ht .line true
  set S' := HeckeShapiro.localCorrespondence htr
  have hex : ∀ s : (goodLineCosets p).representatives, ∃ s' ∈ S'.representatives,
      (gammaL.val⁻¹ * s.val * gammaL.val)⁻¹ * s' ∈ fixedPointLevel rationalLevel (cuspFlag .line true) := by
    rintro ⟨s, hs⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨a, b, hab⟩ := rExpl_double p hp3 i
    obtain ⟨r, hr, hrl⟩ := t.complete (gammaL⁻¹ * a) (b * gammaL)
    rw [hg] at hrl
    have hrl' : r⁻¹ * (gammaL.val⁻¹ * rExpl p i * gammaL.val) ∈ rationalLevel := by
      rw [hab]
      simpa [mul_assoc] using hrl
    refine ⟨HeckeShapiro.shifted htr r, ?_, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
    · rw [HeckeShapiro.localCorrespondence_representatives]
      exact Finset.mem_image_of_mem _ hr
    · have h := rationalLevel.mul_mem (rationalLevel.inv_mem hrl') (HeckeShapiro.transporter_mem htr r)
      have he : (gammaL.val⁻¹ * rExpl p i * gammaL.val)⁻¹ * HeckeShapiro.shifted htr r =
          (r⁻¹ * (gammaL.val⁻¹ * rExpl p i * gammaL.val))⁻¹ * HeckeShapiro.transporter htr r := by
        simp only [HeckeShapiro.shifted]
        group
      rw [he]
      exact h
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (conj_fixes _ (rExpl_fixes p i)))
        (HeckeShapiro.shifted_smul htr hr)
  choose f hfmem hf using hex
  let F : (goodLineCosets p).representatives → S'.representatives := fun s => ⟨f s, hfmem s⟩
  have hinj : Function.Injective F := by
    intro s₁ s₂ h
    apply Subtype.ext
    apply (goodLineCosets p).disjoint s₁.val s₁.property s₂.val s₂.property
    have h12 := (fixedPointLevel rationalLevel (cuspFlag .line true)).mul_mem (hf s₁)
      ((fixedPointLevel rationalLevel (cuspFlag .line true)).inv_mem (hf s₂))
    have hF : f s₁ = f s₂ := congrArg Subtype.val h
    rw [hF] at h12
    have h3 := conj_mem_Λ₁ _ h12
    convert h3 using 1
    group
  have hcard : S'.representatives.card ≤ (goodLineCosets p).representatives.card := by
    rw [HeckeShapiro.localCorrespondence_representatives]
    refine (Finset.card_image_le).trans ?_
    rw [card_representatives p.property t ht hg]
    change _ ≤ (Finset.univ.image (rExpl p)).card
    rw [Finset.card_image_of_injective _ (rExpl_injective p), Finset.card_univ, Fintype.card_sum,
      Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
    apply le_of_eq
    ring
  have hbij : Function.Bijective F := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, le_antisymm (Fintype.card_le_of_injective F hinj) ?_⟩
    simpa only [Fintype.card_coe] using hcard
  exact transport_cohomologyAction rationalLevel (ρn n) gammaL (cuspFlag .line true)
    (QuotientGroup.mk rationalGoodLine) gammaL_smul (goodLineCosets p) S' (Equiv.ofBijective F hbij)
    hf y

/-- **The local `T_p` at the good-line cusp, on the binary edge.** For every away-from-three
correspondence `t` of `Γ diag(p,1,1) Γ` (`p ≠ 3`) and `n > 0`: if the transported class `ψ y` has
vanishing radical restriction, so does `ψ (localOp t y)`, and
`E(ψ(localOp t y)) = E(ψ y) + p^{-(n+1)} T_p E(ψ y)` with `E` the injective binary edge into
`H¹(GL₂(ℤ), Sym^{n+1})` (twist `0`) and `ψ` the injective transport to `Λ₁`. -/
theorem edgeK_localOp (hn : 0 < n) (t : HeckeCorrespondence) (ht : AwayThree t)
    (hg : t.g = gP p.property) (hp3 : p.val ≠ 3) (y : CuspH2 n trivialCharacter .line true)
    (hy : psiL n y ∈ KL n) :
    ∃ h : psiL n (localOp n trivialCharacter t ht .line true y) ∈ KL n,
      edgeK n hn ⟨psiL n (localOp n trivialCharacter t ht .line true y), h⟩ =
        edgeK n hn ⟨psiL n y, hy⟩ + ((p.val : ℂ) ^ (n + 1))⁻¹ •
          LevelOneHeckeH1.arithmeticHecke (n + 1) 0 p (edgeK n hn ⟨psiL n y, hy⟩) := by
  have e := transport_localOp n p t ht hg hp3 y
  refine ⟨e ▸ heckeK_mem n p _ hy, ?_⟩
  have h := edgeK_hecke n p hn _ hy
  convert h using 3

/-- The same for the `T_p` correspondence `TpExistence.tp p`. -/
theorem edgeK_localOp_tp (hn : 0 < n) (hp3 : p.val ≠ 3) (y : CuspH2 n trivialCharacter .line true)
    (hy : psiL n y ∈ KL n) :
    ∃ h : psiL n (localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
        .line true y) ∈ KL n,
      edgeK n hn ⟨psiL n (localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
          .line true y), h⟩ =
        edgeK n hn ⟨psiL n y, hy⟩ + ((p.val : ℂ) ^ (n + 1))⁻¹ •
          LevelOneHeckeH1.arithmeticHecke (n + 1) 0 p (edgeK n hn ⟨psiL n y, hy⟩) :=
  edgeK_localOp n p hn _ _ (TpExistence.tp_g p) hp3 y hy

end TernaryPeriodPolynomials.Spectral.GoodLineLocalOp
