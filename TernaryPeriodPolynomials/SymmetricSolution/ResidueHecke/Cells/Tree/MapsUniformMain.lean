module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Tree.MapsUniform

@[expose] public section


/-!
# Lemma B.1: the comparison scalar is independent of the degree (`PHCompatUniform`)

Formalized by Claude Sonnet 5.5.

In `FaceMain` the constants of the tree formula were produced by existential statements for each `n` separately.  Here the dependence on
`n` is removed: the Schur scalar of `Schur_scalar` is the universal `c₀` of `psiInst_universal` (`treeData_universal`, so the constant of
`edge₂ κ (treeY x)` is `-c₀ / |ker π|` for all `n`: `tree_kappa_uniform`), the constant `cB` of `FidL_eq_coeff` was already chosen before `n`
(`tree_cell_uniform`), and the stabilizer factor `2 / [P_H : P_N]` does not depend on `n`.  Hence `faceEvalAvgUniform_literal`, and with
the explicit scalar `[G : Γ(6)] / ([P_H : P_N] c)` of `residuePeriodAlg_eq_of_avg`, `phCompatUniform_literal`.
-/

open CategoryTheory MonoidalCategory Representation Limits
open scoped TensorProduct

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPeriodPolynomials.Argument.HochschildSerre
open TernaryPeriodPolynomials.Argument.GroupHomologyDescent (T2 U2)

section FUniv

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (eU : U2 ≃* U)
  (R : ProjectiveResolution (Rep.trivial ℚ P ℚ))
  {L P1' P0' : Rep.{0} ℚ (P ⧸ U)} (d' : P1' ⟶ P0') (ε' : P0' ⟶ Rep.trivial ℚ (P ⧸ U) ℚ)
  (hdε : d' ≫ ε' = 0) (hS : (ShortComplex.mk d' ε' hdε).ShortExact)
  (t3 : L ⊗ P1' ⟶ (Phi U).obj (R.complex.X 3)) (t2 : L ⊗ P0' ⟶ (Phi U).obj (R.complex.X 2))
  (hi : t3 ≫ (Phi U).map (R.complex.d 3 2) = (L ◁ d') ≫ t2)
  (hii : t2 ≫ (Phi U).map (R.complex.d 2 1) = 0) (ℓ₀ : L.V)
  (A : Rep.{0} ℚ P) [Representation.IsTrivial (A.ρ.comp U.subtype)] [Module.Finite ℚ A.V]
  (hA : ∀ u : U, A.ρ u = 1) {Γ : Type} [Group Γ] (π : P ⧸ U →* Γ) (D : Rep.{0} ℚ Γ) (lin : A.V ≃ₗ[ℚ] D.V)
  (hcompat : ∀ (g : P) (a : A.V), lin (deltaG eU g • A.ρ g a) = D.ρ (π (QuotientGroup.mk g)) (lin a))

theorem fmap_universal (c₀ : ℚ)
    (hc : ∀ a : A.V, (PsiInst U A R d' ε' hdε hS t3 t2 hi hii).hom (a ⊗ₜ[ℚ] ℓ₀) =
      c₀ • (HomologicalComplex.homologyMap (fZ U R A) 2).hom (gammaEquiv eU hA a)) (a : A.V) :
    (PsiInst U A R d' ε' hdε hS t3 t2 hi hii ≫
      (eR U A R π D (homologyIsoRes eU hA D π lin hcompat)).hom).hom (a ⊗ₜ[ℚ] ℓ₀) = c₀ • lin a := by
  have hH : (inv (HomologicalComplex.homologyMap (fZ U R A) 2)).hom
      ((HomologicalComplex.homologyMap (fZ U R A) 2).hom (gammaEquiv eU hA a)) = gammaEquiv eU hA a := by
    have := congrArg (fun m => Rep.Hom.hom m (gammaEquiv eU hA a))
      (IsIso.hom_inv_id (HomologicalComplex.homologyMap (fZ U R A) 2))
    exact this
  change (homologyIsoRes eU hA D π lin hcompat).hom.hom
    ((inv (HomologicalComplex.homologyMap (fZ U R A) 2)).hom
      ((PsiInst U A R d' ε' hdε hS t3 t2 hi hii).hom (a ⊗ₜ[ℚ] ℓ₀))) = _
  rw [hc a, map_smul, hH, map_smul]
  congr 1
  change lin ((gammaEquiv eU hA).symm ((gammaEquiv eU hA) a)) = lin a
  rw [LinearEquiv.symm_apply_apply]

end FUniv


section TreeUniform

open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPoly.SinglePoleCoordinate (BinaryV)

theorem exists_ne_zero_fib (n : ℕ) : ∃ a : (FibRep n).V, a ≠ 0 := by
  have hq : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ (n + 1) ∈ BinaryV (n + 1) := by
    rw [BinaryV, MvPolynomial.mem_homogeneousSubmodule]
    simpa using (MvPolynomial.isHomogeneous_X ℚ (0 : Fin 2)).pow (n + 1)
  refine ⟨(fiberLin n).symm ⟨_, hq⟩, fun h => ?_⟩
  have h2 := congrArg (fiberLin n) h
  rw [LinearEquiv.apply_symm_apply, map_zero] at h2
  have h3 := congrArg Subtype.val h2
  exact pow_ne_zero _ (MvPolynomial.X_ne_zero (0 : Fin 2)) h3

theorem treeData_universal :
    ∃ c₀ : ℚ, c₀ ≠ 0 ∧ ∀ (n : ℕ) (a : (FibRep n).V),
      (PsiInst U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) (epsQ pibar) (resD1_epsQ pibar)
        (sesQ_shortExact pibar) treeData.t3 treeData.t2 treeData.hi treeData.hii ≫
        (eR U (FibRep n) (RG_projRes PH) pibar (Dplain (n + 1)) (treeE n)).hom).hom
        (a ⊗ₜ[ℚ] treeData.ℓ₀) = c₀ • fiberLin n a := by
  obtain ⟨c₀, hc₀⟩ := psiInst_universal U eU (RG_projRes PH) (Rep.resMap pibar d1) (epsQ pibar)
    (resD1_epsQ pibar) (sesQ_shortExact pibar) treeData.t3 treeData.t2 treeData.hi treeData.hii treeData.ℓ₀
  refine ⟨c₀, ?_, fun n a => ?_⟩
  · intro h0
    obtain ⟨a, ha⟩ := exists_ne_zero_fib 0
    have hinj := PsiInst_injective U (FibRep 0) (RG_projRes PH) (Rep.resMap pibar d1) (epsQ pibar)
      (resD1_epsQ pibar) (sesQ_shortExact pibar) treeData.t3 treeData.t2 treeData.hi treeData.hii
      treeData.ℓ₀ treeData.hℓ treeData.hL treeData.h3
    have h1 : (PsiInst U (FibRep 0) (RG_projRes PH) (Rep.resMap pibar d1) (epsQ pibar) (resD1_epsQ pibar)
        (sesQ_shortExact pibar) treeData.t3 treeData.t2 treeData.hi treeData.hii).hom
        (a ⊗ₜ[ℚ] treeData.ℓ₀) = 0 := by
      rw [hc₀ (FibRep 0) (hA_fib 0) a, h0, zero_smul]
    have h2 : a ⊗ₜ[ℚ] treeData.ℓ₀ = 0 := hinj (h1.trans (map_zero _).symm)
    apply ha
    have h3 := congrArg (iotaM U (FibRep 0) treeData.ℓ₀ treeData.hℓ) h2
    rw [iotaM_tmul, coefL_spec, one_smul, map_zero] at h3
    exact h3
  · exact fmap_universal U eU (RG_projRes PH) (Rep.resMap pibar d1) (epsQ pibar) (resD1_epsQ pibar)
      (sesQ_shortExact pibar) treeData.t3 treeData.t2 treeData.hi treeData.hii treeData.ℓ₀ (FibRep n)
      (hA_fib n) pibar (Dplain (n + 1)) (fiberLin n) (fun g a => fiber_compat n g a) c₀
      (fun a => hc₀ (FibRep n) (hA_fib n) a) a

set_option maxRecDepth 4000 in
theorem tree_kappa_uniform :
    ∃ c₁ : ℚ, c₁ ≠ 0 ∧ ∀ (n : ℕ) (x : KMT treeData n),
      FareyTree.edge2 (Dplain (n + 1)) (kappaLit n (treeY treeData n x)) =
        c₁ • fiberLin n (iotaM U (FibRep n) treeData.ℓ₀ treeData.hℓ
          (evalQ pibar hker_pibar (Abar U (FibRep n) ⊗ treeData.L) x.1)) := by
  obtain ⟨c₀, hc₀, hf⟩ := treeData_universal
  have hcard : (Nat.card pibar.ker : ℚ) ≠ 0 := by
    have : Finite pibar.ker := hker_pibar.to_subtype
    exact_mod_cast (Nat.card_pos (α := pibar.ker)).ne'
  refine ⟨-((Nat.card pibar.ker : ℚ)⁻¹) * c₀,
    mul_ne_zero (neg_ne_zero.2 (inv_ne_zero hcard)) hc₀, fun n x => ?_⟩
  have : Projective (Rep.res pibar P1) := projective_res_P1 pibar hker_pibar
  have : Projective (Rep.res pibar P0) := projective_res_P0 pibar hker_pibar
  have hLam := edge2_hsFarey_LamH U (FibRep n) (RG_projRes PH) pibar pibar_surjective hker_pibar
    (HochschildSerre.isZero_res_three eU (hA_fib n)) (Dplain (n + 1)) (treeE n)
    treeData.t3 treeData.t2 treeData.hi treeData.hii x
  rw [kappaLit_eq, treeY_apply]
  refine hLam.trans ?_
  obtain ⟨a, ha⟩ := one_dim_tmul treeData.ℓ₀ treeData.hℓ treeData.hL
    (evalQ pibar hker_pibar (Abar U (FibRep n) ⊗ treeData.L) x.1)
  have hia : iotaM U (FibRep n) treeData.ℓ₀ treeData.hℓ
      (evalQ pibar hker_pibar (Abar U (FibRep n) ⊗ treeData.L) x.1) = a := by
    rw [ha, iotaM_tmul, coefL_spec, one_smul]
  rw [hia]
  change (-((Nat.card pibar.ker : ℚ)⁻¹)) • (PsiInst U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1)
    (epsQ pibar) (resD1_epsQ pibar) (sesQ_shortExact pibar) treeData.t3 treeData.t2 treeData.hi treeData.hii ≫
      (eR U (FibRep n) (RG_projRes PH) pibar (Dplain (n + 1)) (treeE n)).hom).hom
        (evalQ pibar hker_pibar (Abar U (FibRep n) ⊗ treeData.L) x.1) = _
  rw [ha, hf n a, smul_smul]

end TreeUniform

section CellUniform

open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
open TernaryPoly.OrdinaryResidueSupport (axis)
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.BinaryDuality
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport TernaryPoly.SinglePoleCoordinate
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry
open TernaryPeriodPolynomials.FreeResolution TernaryPeriodPolynomials.TopVanishing GeneralEisenstein
open scoped Classical Pointwise

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem tree_cell_uniform :
    ∃ c₂ : ℚ, c₂ ≠ 0 ∧ ∀ (n : ℕ) (w : groupHomology (Rep.res PN.subtype (FibRep n)) 3),
      avgN PN (FibRep n) 3 w = w →
      ∀ x : KMT treeData n, treeY treeData n x = corN PN (FibRep n) 3 w → FidL n w = c₂ • treeEv treeData n x := by
  obtain ⟨cB, hcB, hFid⟩ := FidL_eq_coeff
  have hcard : (Fintype.card (PH ⧸ PN) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := PH ⧸ PN)).ne'
  refine ⟨cB * (2 * (Fintype.card (PH ⧸ PN) : ℚ)⁻¹), mul_ne_zero hcB (mul_ne_zero two_ne_zero (inv_ne_zero hcard)),
    fun n w hw x hx => ?_⟩
  obtain ⟨ζ, hζ, hcl⟩ := exists_cycleClass (CxN PN (YAR (RG_projRes PH) (FibRep n)))
    ((eNR PN (RG_projRes PH) (FibRep n) 3).hom.hom w)
  have h4N := CxN_d_four PN (FibRep n) (RG_projRes PH) (RG_projRes_d_four PH)
  have h4K := CxK_d_four (FibRep n) (RG_projRes PH) (RG_projRes_d_four PH)
  obtain ⟨hav, hζtr, hz', hclK⟩ := invariant_of_avgN_fixed PN (RG_projRes PH) (FibRep n) h4N w hw ζ hζ hcl
  have hlam := eKR_inv_LamH U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) treeData.t3 treeData.t2 treeData.hi x
  have hq : ((QY PN (YAR (RG_projRes PH) (FibRep n))).f 3).hom ζ =
      lamChain U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) treeData.t3 x := by
    refine cycleClass_injective_top (CxK (YAR (RG_projRes PH) (FibRep n))) h4K _ _ hz'
      (lamChain_cycle U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) treeData.t3 treeData.t2 treeData.hi x) ?_
    rw [hclK, ← hx]
    exact hlam
  have hζ' : ζ = ((trY PN (YAR (RG_projRes PH) (FibRep n))).f 3).hom
      (lamChain U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) treeData.t3 x) := by
    rw [← hq]
    exact hζtr
  have hz := pushRG_cycle n ζ hζ
  have hzw := pushRG_iotaStar n w ζ hζ hcl
  rw [hFid n w _ hz hzw]
  have hC' := tree_chain treeData n x
  rw [← hζ'] at hC'
  change cB • literalFiberMap n 0 (Cmap n ζ) = _
  rw [hC', map_smul, smul_smul]
  rfl

/-- **The uniform averaged face evaluation**: one constant for all degrees `n`. -/
theorem faceEvalAvgUniform_literal : FaceEvalAvgUniform := by
  obtain ⟨c₁, hc₁, hκ⟩ := tree_kappa_uniform
  obtain ⟨c₂, hc₂, hcell⟩ := tree_cell_uniform
  refine ⟨c₂ / c₁, div_ne_zero hc₂ hc₁, fun n w => ?_⟩
  have hidem : avgN PN (FibRep n) 3 (avgN PN (FibRep n) 3 w) = avgN PN (FibRep n) 3 w :=
    avgN_idem (card_ne_zero_gen PN) w
  obtain ⟨x, hx⟩ := treeY_surjective treeData n (corN PN (FibRep n) 3 w)
  have hcor : corN PN (FibRep n) 3 (avgN PN (FibRep n) 3 w) = corN PN (FibRep n) 3 w :=
    corN_avgN_gen w
  have hκ' : (((Statements.BinaryDuality.periodEquivHomology' (n + 1)) (kappaLit n (treeY treeData n x)) :
      OrdinaryResiduePeriod.periodSpace (n + 1)) : BinaryV (n + 1)) = c₁ • treeEv treeData n x :=
    periodEquiv_edge2 (n + 1) (kappaLit n (treeY treeData n x)) _ c₁ (hκ n x)
  rw [hcell n _ hidem x (hx.trans hcor.symm), ← hx, hκ', smul_smul, div_mul_cancel₀ _ hc₁]

/-- **Lemma B.1, uniform residue comparison**: one nonzero scalar `c`, independent of `n` and of the class, with
`edge₂ ∘ κ ∘ Sh = c · res_H` in every degree. -/
theorem phCompatUniform_literal : PHCompatUniform :=
  phCompatUniform_of_faceEvalAvgUniform' faceEvalAvgUniform_literal

end CellUniform

end TernaryPeriodPolynomials.Argument.AppendixBResidue
