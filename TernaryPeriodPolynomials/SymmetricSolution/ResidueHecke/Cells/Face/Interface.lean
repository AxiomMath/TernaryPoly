module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Face.Support
public import TernaryPeriodPolynomials.GroupCohomology.Homology.MapSquare

@[expose] public section


/-!
# Lemma B.1, boundary route: `FaceEval` at the identity apartment, in averaged form

Formalized by Claude Sonnet 5.5.

* `conj_iota_comm`: `ι_*` commutes with the conjugation action of `s ∈ P_H`
  (`cAct` on `H₃(P_N, 𝓡_{n,H₀})` and on `H₃(Γ(6), 𝓡_n)`), by `GroupHomology.map_square` and `rho_PH_lof`;
* `termF_translate`: `termF y s = termF (c_s y) 1` for `s ∈ P_H` (equivariance `neatDualityG` of the neat duality);
* `termF_one`: `termF y 1 = lit₀(comp₀(groupApartmentEvaluation (ι_* y)))`, i.e. the quantity computed by the apartment
  evaluator `Lemma33.Retract.FlatIntersectionBridge` (`evaluation = κ · dT0 · coeffAtT0`);
* `FidL`: that quantity as a linear map of `w ∈ H₃(P_N, 𝓡_{n,H₀})`; `FaceEvalAvg n`: the identity `FidL (avg w) =
  c · edge₂ κ (cor w)` (the cleanest neat-level form of the remaining content of Lemma B.1);
* `faceEvalMain_of_avg`, `phCompat_of_faceEvalAvg`, `faceEvalAvg_of_phCompat`, `phCompat_iff_faceEvalAvg`: `FaceEvalAvg n` is
  equivalent to `PHCompat n`, given the coefficient naturality of the neat duality (the support clause);
  `residuePeriodAlg_eq_of_avg` gives the explicit scalar `[G:Γ(6)] / ([P_H:P_N] c)`, and `FaceEvalAvgUniform`,
  `phCompatUniform_of_faceEvalAvgUniform` the version with one scalar for all `n`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.ModThreeGoodAction IntegralGL3Congruence CategoryTheory
open TernaryPoly.OrdinaryResidueSupport (axis)
open TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport TernaryPoly.SinglePoleCoordinate
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology

theorem jPN_coe (p : PN) : ((jPN p : principalSix) : IntegralGL) = ((p : PH) : IntegralGL) := rfl

theorem conj_jPN (s : PH) :
    (conjN principalSix s.1).comp jPN = jPN.comp (conjN PN s) := by
  refine MonoidHom.ext fun p => Subtype.ext ?_
  change (conjN principalSix s.1 (jPN p) : IntegralGL) = (jPN (conjN PN s p) : IntegralGL)
  rw [conjN_coe, jPN_coe, jPN_coe, conjN_coe]
  rfl

theorem conj_lofN (n : ℕ) (s : PH) :
    (lofN n ≫ (Rep.resFunctor jPN).map (conjRep principalSix (ResRep n) s.1)).hom.toLinearMap =
      (conjRep PN (FibRep n) s ≫ (Rep.resFunctor (conjN PN s)).map (lofN n)).hom.toLinearMap := by
  apply LinearMap.ext
  intro a
  exact rho_PH_lof n s.2 a

theorem conj_iota_comm (n : ℕ) (s : PH) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) :
    cAct principalSix (ResRep n) 3 s.1 (iotaStar n y) =
      iotaStar n (cAct PN (FibRep n) 3 s y) :=
  congrArg (fun m => m.hom y)
    (map_square (k := ℚ) (conjN PN s) (conjN principalSix s.1) jPN jPN (conj_jPN s)
      (lofN n) (conjRep principalSix (ResRep n) s.1) (conjRep PN (FibRep n) s) (lofN n)
      (conj_lofN n s) 3)

/-- **Conjugation by `s ∈ P_H` reduces the translate to the identity apartment**:
`termF y s = termF (c_s y) 1`, `c_s` the conjugation on `H₃(P_N, 𝓡_{n,H₀})`. -/
theorem termF_translate (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) (s : PH) :
    termF n y s.1 = termF n (cAct PN (FibRep n) 3 s y) 1 := by
  have h := congrArg (fun Φ => Φ (OrdinaryApartmentPresentation.frameCycle 1))
    (neatDualityG n s.1 (iotaStar n y))
  rw [conj_iota_comm] at h
  unfold termF
  have h1 : TernaryPeriodPolynomials.Argument.GroupHomology.term stG (ResRep n).ρ (psiN n y) s.1
      (OrdinaryApartmentPresentation.frameCycle 1) = psiN n (cAct PN (FibRep n) 3 s y)
        (OrdinaryApartmentPresentation.frameCycle 1) := h.symm
  rw [h1]
  simp [TernaryPeriodPolynomials.Argument.GroupHomology.term]

/-- At `g = 1` the residue is the `a = 0` component of the apartment evaluation of `ι_* y`. -/
theorem termF_one (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) :
    termF n y 1 = literalFiberMap n 0 (SinglePoleSupport.component n (axis 0)
      ((OrdinaryTopBoundaryComparison.groupApartmentEvaluation
        (Rep.res principalSix.subtype (ResRep n))).hom (iotaStar n y))) := by
  unfold termF
  simp only [TernaryPeriodPolynomials.Argument.GroupHomology.term, inv_one, map_one,
    Module.End.one_apply]
  have := thetaGen_refl_apply (ResRep n) (iotaStar n y)
  refine congrArg (fun v => literalFiberMap n 0 (SinglePoleSupport.component n (axis 0) v)) ?_
  change (psiGen principalSix (MulEquiv.refl ↥principalSix) (ResRep n) (iotaStar n y))
    (OrdinaryApartmentPresentation.frameCycle 1) = _
  unfold psiGen
  rw [LinearMap.comp_apply, this]
  rfl

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The identity-apartment `a = 0` residue of the neat functional of `ι_* w`, as a linear map of `w`:
`w ↦ lit₀(comp₀(ev_{σ₀}(ι_* w)))`. -/
def FidL (n : ℕ) : groupHomology (Rep.res PN.subtype (FibRep n)) 3 →ₗ[ℚ] BinaryV (n + 1) :=
  (literalFiberMap n 0).comp ((SinglePoleSupport.component n (axis 0)).comp
    ((OrdinaryTopBoundaryComparison.groupApartmentEvaluation
      (Rep.res principalSix.subtype (ResRep n))).hom.comp (iotaStar n)))

theorem termF_one_eq_FidL (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) :
    termF n y 1 = FidL n y := termF_one n y

/-- **`FaceEval` in averaged form**: the identity-apartment residue of `ι_*` of the `P_H/P_N`-average of `w` is
`c · edge₂ κ (cor w)`. -/
def FaceEvalAvg (n : ℕ) : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ ∀ w : groupHomology (Rep.res PN.subtype (FibRep n)) 3,
    FidL n (avgN PN (FibRep n) 3 w) =
      c • (((Statements.BinaryDuality.periodEquivHomology' (n + 1)) (kappaLit n (corN PN (FibRep n) 3 w)) :
        OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1))

theorem sum_termF_eq_card_smul_FidL (n : ℕ) (y : groupHomology (Rep.res PN.subtype (FibRep n)) 3) :
    ∑ s : PH ⧸ PN, termF n y ((s.out : PH) : IntegralGL) =
      (Fintype.card (PH ⧸ PN) : ℚ) • FidL n (avgN PN (FibRep n) 3 y) := by
  have h1 : ∑ s : PH ⧸ PN, termF n y ((s.out : PH) : IntegralGL) =
      ∑ s : PH ⧸ PN, FidL n (cAct PN (FibRep n) 3 s.out y) :=
    Finset.sum_congr rfl fun s _ => by rw [termF_translate, termF_one_eq_FidL]
  have h2 : FidL n (avgN PN (FibRep n) 3 y) = ((Fintype.card (PH ⧸ PN) : ℚ)⁻¹) •
      ∑ s : PH ⧸ PN, FidL n (cAct PN (FibRep n) 3 s.out y) := by
    unfold avgN
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  rw [h1, h2, smul_smul, mul_inv_cancel₀ (card_ne_zero_gen PN), one_smul]

theorem faceEvalMain_of_avg (n : ℕ) (h : FaceEvalAvg n) : FaceEvalMain n := by
  obtain ⟨c, hc, hF⟩ := h
  refine ⟨(Fintype.card (PH ⧸ PN) : ℚ) * c, mul_ne_zero (card_ne_zero_gen PN) hc, fun y => ?_⟩
  rw [sum_termF_eq_card_smul_FidL, hF y, smul_smul]

/-- **The explicit scalar**: if `FidL (avg w) = c · edge₂ κ (cor w)` for all `w`, then
`edge₂ ∘ κ ∘ Sh = ([G:Γ(6)] / ([P_H:P_N] c)) · res_H`. -/
theorem residuePeriodAlg_eq_of_avg
    (hnat : ∀ {W W' : Rep.{0} ℚ principalSix} (f : W ⟶ W') (x : groupHomology W 3),
      (OrdinaryTopBoundaryComparison.groupOrdinaryIso W').hom.hom
          ((groupHomology.map (MonoidHom.id principalSix) f 3).hom x) =
        (OrdinaryTopBoundaryComparison.groupOrdinaryIso W).hom.hom x ≫ f)
    (n : ℕ) (c : ℚ) (hc : c ≠ 0)
    (hF : ∀ w : groupHomology (Rep.res PN.subtype (FibRep n)) 3,
      FidL n (avgN PN (FibRep n) 3 w) =
        c • (((Statements.BinaryDuality.periodEquivHomology' (n + 1)) (kappaLit n (corN PN (FibRep n) 3 w)) :
          OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)))
    (x : groupHomology (ResRep n) 3) :
    residuePeriodAlg n x = ((Fintype.card (IntegralGL ⧸ principalSix) : ℚ) /
      ((Fintype.card (PH ⧸ PN) : ℚ) * c)) • resHLit n x := by
  have hcG := card_ne_zero_gen principalSix
  have hcP := card_ne_zero_gen PN
  obtain ⟨y, hy⟩ := corN_surjective (A := FibRep n) (n := 3) (N := PN) hcP (shLit n x)
  have hx : x = (groupHomology.map PH.subtype (lofHom n) 3).hom (corN PN (FibRep n) 3 y) := by
    rw [hy]
    have h1 := congrArg (fun m => m x) (shapiroHomologyIso n 3).hom_inv_id
    refine h1.symm.trans ?_
    rw [shapiroHomologyIso_inv]
    rfl
  apply Subtype.ext
  have e1 : ((residuePeriodAlg n x : OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) =
      (((Statements.BinaryDuality.periodEquivHomology' (n + 1)) (kappaLit n (corN PN (FibRep n) 3 y)) :
        OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) := by
    unfold residuePeriodAlg
    change (((Statements.BinaryDuality.periodEquivHomology' (n + 1)) (kappaLit n (shLit n x)) :
        OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) = _
    rw [← hy]
  have e2 := resHLit_cor_lof n y
  rw [← hx, sum_termF_collapse n y (fun g hg => termF_eq_zero_of_natural hnat n y hg),
    sum_termF_eq_card_smul_FidL, hF y] at e2
  rw [e1]
  change _ = ((Fintype.card (IntegralGL ⧸ principalSix) : ℚ) / ((Fintype.card (PH ⧸ PN) : ℚ) * c)) •
    ((resHLit n x : OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1))
  rw [e2, smul_smul, smul_smul, smul_smul]
  have : (Fintype.card (IntegralGL ⧸ principalSix) : ℚ) / ((Fintype.card (PH ⧸ PN) : ℚ) * c) *
      (Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹ * (Fintype.card (PH ⧸ PN) : ℚ) * c = 1 := by
    field_simp
  rw [this, one_smul]

/-- **`PHCompat` from the averaged neat-level evaluation statement** (given the coefficient naturality of the neat
duality, needed for the support clause). -/
theorem phCompat_of_faceEvalAvg
    (hnat : ∀ {W W' : Rep.{0} ℚ principalSix} (f : W ⟶ W') (x : groupHomology W 3),
      (OrdinaryTopBoundaryComparison.groupOrdinaryIso W').hom.hom
          ((groupHomology.map (MonoidHom.id principalSix) f 3).hom x) =
        (OrdinaryTopBoundaryComparison.groupOrdinaryIso W).hom.hom x ≫ f)
    (n : ℕ) (h : FaceEvalAvg n) : PHCompat n :=
  phCompat_of_faceEvalMain hnat n (faceEvalMain_of_avg n h)

/-- **Sharpness of the reduction**: given the coefficient naturality, `FaceEvalAvg n` is equivalent to `PHCompat n`. -/
theorem faceEvalAvg_of_phCompat
    (hnat : ∀ {W W' : Rep.{0} ℚ principalSix} (f : W ⟶ W') (x : groupHomology W 3),
      (OrdinaryTopBoundaryComparison.groupOrdinaryIso W').hom.hom
          ((groupHomology.map (MonoidHom.id principalSix) f 3).hom x) =
        (OrdinaryTopBoundaryComparison.groupOrdinaryIso W).hom.hom x ≫ f)
    (n : ℕ) (h : PHCompat n) : FaceEvalAvg n := by
  obtain ⟨c, hc, hP⟩ := h
  refine ⟨(Fintype.card (IntegralGL ⧸ principalSix) : ℚ) / ((Fintype.card (PH ⧸ PN) : ℚ) * c),
    div_ne_zero (card_ne_zero_gen principalSix) (mul_ne_zero (card_ne_zero_gen PN) hc), fun w => ?_⟩
  set x := (groupHomology.map PH.subtype (lofHom n) 3).hom (corN PN (FibRep n) 3 w) with hx
  have e1 : ((residuePeriodAlg n x : OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) =
      (((Statements.BinaryDuality.periodEquivHomology' (n + 1)) (kappaLit n (corN PN (FibRep n) 3 w)) :
        OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) := by
    unfold residuePeriodAlg
    change (((Statements.BinaryDuality.periodEquivHomology' (n + 1)) (kappaLit n (shLit n x)) :
        OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) = _
    have : shLit n x = corN PN (FibRep n) 3 w := by
      change (shapiroHomologyIso n 3).hom x = _
      rw [hx]
      have h1 := congrArg (fun m => m (corN PN (FibRep n) 3 w)) (shapiroHomologyIso n 3).inv_hom_id
      rw [shapiroHomologyIso_inv] at h1
      exact h1
    rw [this]
  have e2 := resHLit_cor_lof n w
  rw [← hx, sum_termF_collapse n w (fun g hg => termF_eq_zero_of_natural hnat n w hg),
    sum_termF_eq_card_smul_FidL] at e2
  have e3 := congrArg Subtype.val (hP x)
  have hcG := card_ne_zero_gen principalSix
  have hcP := card_ne_zero_gen PN
  have hP' : (((Statements.BinaryDuality.periodEquivHomology' (n + 1)) (kappaLit n (corN PN (FibRep n) 3 w)) :
        OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) =
      c • ((Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹) •
        (Fintype.card (PH ⧸ PN) : ℚ) • FidL n (avgN PN (FibRep n) 3 w) := by
    rw [← e1, e3]
    change c • ((resHLit n x : OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) = _
    rw [e2]
  rw [hP', smul_smul, smul_smul, smul_smul]
  have : (Fintype.card (IntegralGL ⧸ principalSix) : ℚ) / ((Fintype.card (PH ⧸ PN) : ℚ) * c) *
      c * (Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹ * (Fintype.card (PH ⧸ PN) : ℚ) = 1 := by
    field_simp
  rw [this, one_smul]

theorem phCompat_iff_faceEvalAvg
    (hnat : ∀ {W W' : Rep.{0} ℚ principalSix} (f : W ⟶ W') (x : groupHomology W 3),
      (OrdinaryTopBoundaryComparison.groupOrdinaryIso W').hom.hom
          ((groupHomology.map (MonoidHom.id principalSix) f 3).hom x) =
        (OrdinaryTopBoundaryComparison.groupOrdinaryIso W).hom.hom x ≫ f)
    (n : ℕ) : PHCompat n ↔ FaceEvalAvg n :=
  ⟨faceEvalAvg_of_phCompat hnat n, phCompat_of_faceEvalAvg hnat n⟩

/-- The uniform (in `n`) averaged face evaluation. -/
def FaceEvalAvgUniform : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ ∀ (n : ℕ) (w : groupHomology (Rep.res PN.subtype (FibRep n)) 3),
    FidL n (avgN PN (FibRep n) 3 w) =
      c • (((Statements.BinaryDuality.periodEquivHomology' (n + 1)) (kappaLit n (corN PN (FibRep n) 3 w)) :
        OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1))

theorem phCompatUniform_of_faceEvalAvgUniform
    (hnat : ∀ {W W' : Rep.{0} ℚ principalSix} (f : W ⟶ W') (x : groupHomology W 3),
      (OrdinaryTopBoundaryComparison.groupOrdinaryIso W').hom.hom
          ((groupHomology.map (MonoidHom.id principalSix) f 3).hom x) =
        (OrdinaryTopBoundaryComparison.groupOrdinaryIso W).hom.hom x ≫ f)
    (h : FaceEvalAvgUniform) : PHCompatUniform := by
  obtain ⟨c, hc, hF⟩ := h
  exact ⟨(Fintype.card (IntegralGL ⧸ principalSix) : ℚ) / ((Fintype.card (PH ⧸ PN) : ℚ) * c),
    div_ne_zero (card_ne_zero_gen principalSix) (mul_ne_zero (card_ne_zero_gen PN) hc),
    fun n x => residuePeriodAlg_eq_of_avg hnat n c hc (hF n) x⟩

end TernaryPeriodPolynomials.Argument.AppendixBResidue
