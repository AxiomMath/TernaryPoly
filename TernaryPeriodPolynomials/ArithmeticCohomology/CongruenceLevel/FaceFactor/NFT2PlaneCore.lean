module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.NFT2PlaneBar

@[expose] public section


/-!
# NFT-2 for planes, algebraic form

Formalized by Claude Sonnet 5.5.

`nft2_plane_core`: let `zx`, `zy` be two-cocycles of the face group `Q = gammaNPAt 6 (planeFaceRepr i)` with `z̄_d = zx + dκ`, `z̄_e = zy + dκ'`, `zx` vanishing on the radical.  Then there is a normalised `gn` with `dd3T gn = zx ∪ zy`, vanishing on `inl³`,
such that for every flag `F` over the plane of the face the class of `planeTheta` equals the class of the cocycle `zx|_{Stab F} ⌣ (-wn) + gn|_{Stab F}` for a primitive `wn` of `zy|_{Stab F}`.
-/

open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPoly.EquivariantSingularSmall
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FlagH3

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section PlaneCore

theorem dd2_dd1P {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module ℚ M] (ρ : Representation ℚ G M) (κ : G → M) :
    dd2 ρ (dd1 ρ κ) = 0 := by
  funext g h l
  simp only [dd2, dd1, map_mul, Module.End.mul_apply, map_sub, map_add, Pi.zero_apply, mul_assoc]
  abel

theorem dd2_addP {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module ℚ M] (ρ : Representation ℚ G M) (a b : G → G → M) :
    dd2 ρ (a + b) = dd2 ρ a + dd2 ρ b := by
  funext g h l
  simp only [dd2, Pi.add_apply, map_add]
  abel

theorem dTwo_eq_dd2TP {B : Type} [Group B] (ψ : B → B → ℚ) :
    dTwo (fun g : Fin 2 → B => ψ (g 0) (g 1)) = fun g : Fin 3 → B => dd2T ψ (g 0) (g 1) (g 2) := by
  funext g
  rw [dTwo_apply]
  simp [dd2T]

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6))

/-- **NFT-2 (plane, algebraic form).** -/
theorem nft2_plane_core (i : PlaneFaces 6) (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (zx : ↥(gammaNPAt 6 (planeFaceRepr i)) → ↥(gammaNPAt 6 (planeFaceRepr i)) → W)
    (zy : ↥(gammaNPAt 6 (planeFaceRepr i)) → ↥(gammaNPAt 6 (planeFaceRepr i)) → W')
    (κ : ↥(gammaNPAt 6 (planeFaceRepr i)) → W) (κ' : ↥(gammaNPAt 6 (planeFaceRepr i)) → W')
    (hzx : dd2 (W.ρ.comp (planeEmb (planeFaceRepr i))) zx = 0) (hzy : dd2 (W'.ρ.comp (planeEmb (planeFaceRepr i))) zy = 0)
    (h1 : zbarP i d = zx + dd1 (W.ρ.comp (planeEmb (planeFaceRepr i))) κ)
    (h2 : zbarP i e = zy + dd1 (W'.ρ.comp (planeEmb (planeFaceRepr i))) κ')
    (inl : Multiplicative (ℤ × ℤ) →* ↥(gammaNPAt 6 (planeFaceRepr i))) (hinj : Function.Injective inl)
    (hradx : ∀ a b : Multiplicative (ℤ × ℤ), zx (inl a) (inl b) = 0) :
    ∃ gn : ↥(gammaNPAt 6 (planeFaceRepr i)) → ↥(gammaNPAt 6 (planeFaceRepr i)) → ↥(gammaNPAt 6 (planeFaceRepr i)) → ℚ,
      dd3T gn = cup22 (W'.ρ.comp (planeEmb (planeFaceRepr i))) (pairOf π) zx zy ∧
      (∀ a b c : Multiplicative (ℤ × ℤ), gn (inl a) (inl b) (inl c) = 0) ∧
      ∀ (F : Flag) (hF : flagPlaneOf F = planeOf (planeFaceRepr i)),
        ∃ wn : ↥(MulAction.stabilizer Γ6 F) → W',
          dd1 (W'.ρ.comp (MulAction.stabilizer Γ6 F).subtype) wn =
            (fun s t => zy (stabToE (planeFaceRepr i) F hF s) (stabToE (planeFaceRepr i) F hF t)) ∧
          ∃ hΘ : dThree (fun g : Fin 3 → ↥(MulAction.stabilizer Γ6 F) =>
              cup21 (W'.ρ.comp (MulAction.stabilizer Γ6 F).subtype) (pairOf π)
                (fun s t => zx (stabToE (planeFaceRepr i) F hF s) (stabToE (planeFaceRepr i) F hF t)) (-wn) (g 0) (g 1) (g 2) +
              gn (stabToE (planeFaceRepr i) F hF (g 0)) (stabToE (planeFaceRepr i) F hF (g 1))
                (stabToE (planeFaceRepr i) F hF (g 2))) = 0,
          clsRes (MulAction.stabilizer Γ6 F) (planeTheta π d e γ F) (planeTheta_dThree π d e γ hγ F) =
            clsRes (MulAction.stabilizer Γ6 F) _ hΘ := by
  set ρQ : Representation ℚ ↥(gammaNPAt 6 (planeFaceRepr i)) W := W.ρ.comp (planeEmb (planeFaceRepr i)) with hρQ
  set ρQ' : Representation ℚ ↥(gammaNPAt 6 (planeFaceRepr i)) W' := W'.ρ.comp (planeEmb (planeFaceRepr i)) with hρQ'
  have he : ∀ (g : ↥(gammaNPAt 6 (planeFaceRepr i))) (v : W) (w : W'), pairOf π (ρQ g v) (ρQ' g w) = pairOf π v w :=
    fun g v w => pairOf_inv π (planeEmb (planeFaceRepr i) g) v w
  have hγb := gbarP_dd3T π i d e γ hγ
  have hzb : dd2 ρQ (zbarP i d) = 0 := by
    rw [h1, dd2_addP, hzx, dd2_dd1P, add_zero]
  obtain ⟨ε, hε⟩ := nfGamma_exists inl hinj he zx (zbarP i d) zy (zbarP i e) κ κ' (gbarP i γ) hzb hzy h1 h2 hγb hradx
  have hdd := nfGamma0_dd3T he zx (zbarP i d) zy (zbarP i e) κ κ' (gbarP i γ) hzb hzy h1 h2 hγb
  have hgn : dd3T (nfGamma0 ρQ' (pairOf π) (zbarP i d) κ κ' zy (gbarP i γ) - dd2T ε) = cup22 ρQ' (pairOf π) zx zy := by
    rw [dd3T_sub, dd3T_dd2T, hdd, sub_zero]
  refine ⟨nfGamma0 ρQ' (pairOf π) (zbarP i d) κ κ' zy (gbarP i γ) - dd2T ε, hgn, fun a b c => hε a b c, ?_⟩
  intro F hF
  have hρ : ∀ (s : ↥(MulAction.stabilizer Γ6 F)) (v : W), ρQ (stabToE (planeFaceRepr i) F hF s) v =
      (W.ρ.comp (MulAction.stabilizer Γ6 F).subtype) s v := by
    intro s v
    show W.ρ (planeEmb (planeFaceRepr i) (stabToE (planeFaceRepr i) F hF s)) v = W.ρ (s : Γ6) v
    rw [planeEmb_stabToE_gen]
  have hρ' : ∀ (s : ↥(MulAction.stabilizer Γ6 F)) (v : W'), ρQ' (stabToE (planeFaceRepr i) F hF s) v =
      (W'.ρ.comp (MulAction.stabilizer Γ6 F).subtype) s v := by
    intro s v
    show W'.ρ (planeEmb (planeFaceRepr i) (stabToE (planeFaceRepr i) F hF s)) v = W'.ρ (s : Γ6) v
    rw [planeEmb_stabToE_gen]
  have hzF : ∀ g : ↥(MulAction.stabilizer Γ6 F), g • F = F := fun g => g.2
  have hw : dd1 (W'.ρ.comp (MulAction.stabilizer Γ6 F).subtype)
      (fun s => barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) F e.w (fun _ : Fin 1 => s)) =
      fun s t => zbarP i e (stabToE (planeFaceRepr i) F hF s) (stabToE (planeFaceRepr i) F hF t) := by
    funext s t
    rw [bar_dd1 (MulAction.stabilizer Γ6 F) W' (1 : RationalGL3) F hzF e.w s t, e.hw, barCochain_flagPlane, zbarP_flag]
  set ι := stabToE (planeFaceRepr i) F hF with hι
  set wb : ↥(MulAction.stabilizer Γ6 F) → W' :=
    fun s => barCochain (MulAction.stabilizer Γ6 F) (1 : RationalGL3) F e.w (fun _ : Fin 1 => s) with hwb
  have hwn := nf_primitiveP ι hρ' zy (zbarP i e) κ' h2 wb hw
  have heH := pull_inv ι hρ hρ' he
  have hΘ := nfThetaP_dd3T ι hρ hρ' heH zx zy (nfGamma0 ρQ' (pairOf π) (zbarP i d) κ κ' zy (gbarP i γ) - dd2T ε) hzx hgn
    (wb - fun s => κ' (ι s)) hwn
  have hΘ' : dThree (fun g : Fin 3 → ↥(MulAction.stabilizer Γ6 F) =>
      cup21 (W'.ρ.comp (MulAction.stabilizer Γ6 F).subtype) (pairOf π) (fun s t => zx (ι s) (ι t)) (-(wb - fun s => κ' (ι s)))
        (g 0) (g 1) (g 2) +
      (nfGamma0 ρQ' (pairOf π) (zbarP i d) κ κ' zy (gbarP i γ) - dd2T ε) (ι (g 0)) (ι (g 1)) (ι (g 2))) = 0 := by
    rw [dThree_eq_dd3T (fun a b c => cup21 (W'.ρ.comp (MulAction.stabilizer Γ6 F).subtype) (pairOf π) (fun s t => zx (ι s) (ι t))
        (-(wb - fun s => κ' (ι s))) a b c +
      (nfGamma0 ρQ' (pairOf π) (zbarP i d) κ κ' zy (gbarP i γ) - dd2T ε) (ι a) (ι b) (ι c))]
    funext g
    exact congrFun (congrFun (congrFun (congrFun hΘ (g 0)) (g 1)) (g 2)) (g 3)
  refine ⟨wb - fun s => κ' (ι s), hwn, hΘ', ?_⟩
  have hT := nfThetaP_eq ι hρ hρ' he zx (zbarP i d) zy (zbarP i e) κ κ' (gbarP i γ) ε h1 h2 wb hw
  have hL : planeTheta π d e γ F = fun g : Fin 3 → ↥(MulAction.stabilizer Γ6 F) =>
      cup21 (W'.ρ.comp (MulAction.stabilizer Γ6 F).subtype) (pairOf π) (fun s t => zbarP i d (ι s) (ι t)) (-wb) (g 0) (g 1) (g 2) +
        gbarP i γ (ι (g 0)) (ι (g 1)) (ι (g 2)) := by
    rw [← planeTheta_hfun π d e γ F]
    funext g
    have hg : g = ![g 0, g 1, g 2] := by funext j; fin_cases j <;> rfl
    simp only [hwb]
    congr 1
    · congr 1
      funext s t
      exact (zbarP_flag i F hF d s t).symm
    · rw [gbarP_flag i F hF γ (g 0) (g 1) (g 2), ← hg]
  unfold clsRes
  congr 1
  refine cocycleClass_eq_of_dTwo _ _ _ _
    (fun g : Fin 2 → ↥(MulAction.stabilizer Γ6 F) =>
      ((fun s t : ↥(MulAction.stabilizer Γ6 F) => ε (ι s) (ι t)) -
        cup11 (W'.ρ.comp (MulAction.stabilizer Γ6 F).subtype) (pairOf π) (fun s => κ (ι s)) (wb - fun s => κ' (ι s))) (g 0) (g 1)) ?_
  rw [dTwo_eq_dd2TP, hL]
  funext g
  exact congrFun (congrFun (congrFun hT (g 0)) (g 1)) (g 2)

end PlaneCore

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
