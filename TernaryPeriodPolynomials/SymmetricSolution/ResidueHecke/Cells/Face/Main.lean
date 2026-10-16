module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Tree.Data
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.LamClass
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.T3Chain
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Top
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Face.Assembly
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.FidLBridge
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.EvalQChar
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Stab

@[expose] public section


/-!
# Lemma B.1: `FaceEvalAvg` from the tree data of the oriented cell resolution

Formalized by Claude Sonnet 5.5.

`TreeData` packages the one-dimensional `P_H/U`-module `L` and the equivariant tree maps `t₃ : L ⊗ P1 → Φ(RG₃)`,
`t₂ : L ⊗ P0 → Φ(RG₂)` of the oriented cell resolution (hypotheses of the tree theorem, the non-vanishing of `t₂(ℓ₀ ⊗ s₀)`,
and the normalization `t₃(ℓ₀ ⊗ edgeGen) = [⟨T₀⟩]`).  Given such data, `faceEvalAvg_of_tree` proves `FaceEvalAvg n`:

* `treeY` parametrizes `H₃(P_H, 𝓡_{n,H₀})` by the kernel `K_M` (`treeY_surjective`, from the tree theorem and the
  isomorphism `Ψ'`), and `tree_kappa` computes `edge₂ κ` of `treeY x` (Schur's lemma for `Sym^{n+1}`);
* `tree_chain` computes the coefficient at `T₀` of the transfer of the cell cycle attached to `x`: the stabilizer sum of `T3Chain`,
  matched with the `evalQ`-side by `stab_sum_eq`;
* `tree_cell` combines this with the flat bridge `FidL_eq_coeff` and the cell push-forward `pushRG`.
-/

open CategoryTheory MonoidalCategory Representation Limits
open scoped TensorProduct

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
open TernaryPoly.OrdinaryResidueSupport (axis)
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.HochschildSerre
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.BinaryDuality
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport TernaryPoly.SinglePoleCoordinate
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
open TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry
open TernaryPeriodPolynomials.FreeResolution TernaryPeriodPolynomials.TopVanishing GeneralEisenstein
open scoped Classical Pointwise


attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem periodEquiv_edge2 (d : ℕ) (y : groupHomology (Dplain d) 1) (v : (Dplain d).V) (c : ℚ)
    (h : FareyTree.edge2 (Dplain d) y = c • v) :
    (((Statements.BinaryDuality.periodEquivHomology' d) y : OrdinaryResiduePeriod.periodSpace d) : BinaryV d) =
      c • (v : BinaryV d) := by
  rw [Statements.BinaryDuality.periodEquivHomology'_apply]
  exact h

/-- The iso `H₂(ZP) ≅ Res 𝓓` used in `kappaLit`. -/
def treeE (n : ℕ) : (ZP U (FibRep n)).homology 2 ≅ Rep.res pibar (Dplain (n + 1)) :=
  homologyIsoRes eU (fun u => FibRep_U n u) (Dplain (n + 1)) pibar (fiberLin n) (fun g a => fiber_compat n g a)

theorem hker_pibar : (pibar.ker : Set (PH ⧸ U)).Finite := by
  have := finite_ker_pibar
  exact Set.toFinite _

theorem hA_fib (n : ℕ) : ∀ u : U, (FibRep n).ρ u = 1 := fun u => FibRep_U n u

theorem kappaLit_eq (n : ℕ) :
    kappaLit n = hsFarey U (FibRep n) pibar pibar_surjective hker_pibar
      (HochschildSerre.isZero_res_three eU (hA_fib n)) (Dplain (n + 1)) (treeE n) := rfl

/-- The type of the kernel `K_M` for the tree data. -/
abbrev KMT (T : TreeData) (n : ℕ) : Type :=
  KM (Rep.res pibar P1) (Rep.res pibar P0) (Rep.resMap pibar d1) (Abar U (FibRep n) ⊗ T.L)

theorem hL_char (T : TreeData) (q : PH ⧸ U) :
    T.L.ρ q = (((pibar q).val.det : ℤ) : ℚ) • LinearMap.id := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
  rw [L_character U (RG_projRes PH) (Rep.resMap pibar d1) (epsQ pibar) (resD1_epsQ pibar)
    (sesQ_shortExact pibar) T.t3 T.t2 T.hi T.hii eU T.ℓ₀ T.hℓ T.hL T.h3 p, deltaG_eq]
  rfl

/-- The parametrization `x ↦ (ZIsoR)⁻¹ Λ x` of `H₃(P_H, 𝓡_{n,H₀})` by the kernel `K_M`. -/
def treeY (T : TreeData) (n : ℕ) : KMT T n →ₗ[ℚ] groupHomology (FibRep n) 3 :=
  ((groupHomologyZIsoR U (RG_projRes PH) (FibRep n) 3).inv.hom).comp
    (LamH (ZR U (RG_projRes PH) (FibRep n)) (Rep.res pibar P1) (Rep.res pibar P0) (Rep.resMap pibar d1)
      (Abar U (FibRep n) ⊗ T.L) (ThetaIn U (FibRep n) (RG_projRes PH) T.t3)
      (ThetaIn U (FibRep n) (RG_projRes PH) T.t2)
      (ThetaIn_comm U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) T.t3 T.t2 T.hi))

theorem treeY_apply (T : TreeData) (n : ℕ) (x : KMT T n) :
    treeY T n x = (groupHomologyZIsoR U (RG_projRes PH) (FibRep n) 3).inv.hom
      (LamH (ZR U (RG_projRes PH) (FibRep n)) (Rep.res pibar P1) (Rep.res pibar P0) (Rep.resMap pibar d1)
        (Abar U (FibRep n) ⊗ T.L) (ThetaIn U (FibRep n) (RG_projRes PH) T.t3)
        (ThetaIn U (FibRep n) (RG_projRes PH) T.t2)
        (ThetaIn_comm U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) T.t3 T.t2 T.hi) x) := rfl

set_option maxRecDepth 4000 in
theorem tree_kappa (T : TreeData) (n : ℕ) :
    ∃ c₁ : ℚ, c₁ ≠ 0 ∧ ∀ x : KMT T n,
      FareyTree.edge2 (Dplain (n + 1)) (kappaLit n (treeY T n x)) =
        c₁ • fiberLin n (iotaM U (FibRep n) T.ℓ₀ T.hℓ
          (evalQ pibar hker_pibar (Abar U (FibRep n) ⊗ T.L) x.1)) := by
  have : Projective (Rep.res pibar P1) := projective_res_P1 pibar hker_pibar
  have : Projective (Rep.res pibar P0) := projective_res_P0 pibar hker_pibar
  obtain ⟨c₁, hc₁, hκ⟩ := edge2_hsFarey_tree U (FibRep n) eU (RG_projRes PH) pibar pibar_surjective hker_pibar
    (HochschildSerre.isZero_res_three eU (hA_fib n)) (n + 1) (fiberLin n) (fun g a => fiber_compat n g a)
    (treeE n) T.ℓ₀ T.hℓ T.hL T.t3 T.t2 T.hi T.hii T.h3
  refine ⟨c₁, hc₁, fun x => ?_⟩
  rw [kappaLit_eq, treeY_apply]
  exact hκ x

theorem exists_stab_finset : ∃ S : Finset PH, ∀ h, h ∈ S ↔ glGraded 3 h.1 T0g = T0g := by
  have hfin : Finite {g : IntegralGL3 // g • T0set = T0set} := finite_stab_lines T0set T0_spans
  have hinj : Function.Injective (fun h : {h : PH // glGraded 3 h.1 T0g = T0g} =>
      (⟨h.1.1, by
        have := congrArg (fun C : Graded 3 => C.1.val) h.2
        exact this⟩ : {g : IntegralGL3 // g • T0set = T0set})) := by
    intro h h' hh
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun g : {g : IntegralGL3 // g • T0set = T0set} => g.1) hh)
  have : Finite {h : PH // glGraded 3 h.1 T0g = T0g} := Finite.of_injective _ hinj
  have hS : {h : PH | glGraded 3 h.1 T0g = T0g}.Finite := Set.finite_coe_iff.mp this
  exact ⟨hS.toFinset, fun h => by simp⟩

theorem treeY_surjective (T : TreeData) (n : ℕ) : Function.Surjective (treeY T n) := by
  have : Projective (Rep.res pibar P1) := projective_res_P1 pibar hker_pibar
  have : Projective (Rep.res pibar P0) := projective_res_P0 pibar hker_pibar
  have hU3 := HochschildSerre.isZero_res_three eU (hA_fib n)
  have hiso : IsIso (PsiInst U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) (epsQ pibar) (resD1_epsQ pibar)
      (sesQ_shortExact pibar) T.t3 T.t2 T.hi T.hii) :=
    PsiInst_isIso U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) (epsQ pibar) (resD1_epsQ pibar)
      (sesQ_shortExact pibar) T.t3 T.t2 T.hi T.hii eU (hA_fib n) T.ℓ₀ T.hℓ T.hL T.h3
  have hiso' : IsIso (PsiPrime (ZR U (RG_projRes PH) (FibRep n)) (Rep.res pibar P1) (Rep.res pibar P0)
      (Rep.resMap pibar d1) (epsQ pibar) (resD1_epsQ pibar) (Abar U (FibRep n) ⊗ T.L) (sesQ_shortExact pibar)
      (ThetaIn U (FibRep n) (RG_projRes PH) T.t3) (ThetaIn U (FibRep n) (RG_projRes PH) T.t2)
      (ThetaIn_comm U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) T.t3 T.t2 T.hi)
      (ThetaIn_cyc U (FibRep n) (RG_projRes PH) T.t2 T.hii)) := hiso
  have hbij := LamH_bijective (ZR U (RG_projRes PH) (FibRep n)) (Rep.res pibar P1) (Rep.res pibar P0)
    (Rep.resMap pibar d1) (epsQ pibar) (resD1_epsQ pibar) (Abar U (FibRep n) ⊗ T.L) (sesQ_shortExact pibar)
    (ThetaIn U (FibRep n) (RG_projRes PH) T.t3) (ThetaIn U (FibRep n) (RG_projRes PH) T.t2)
    (ThetaIn_comm U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) T.t3 T.t2 T.hi)
    (ThetaIn_cyc U (FibRep n) (RG_projRes PH) T.t2 T.hii) (ZR_projective U (RG_projRes PH) (FibRep n))
    (isZero_ZR_homology_of_group U (RG_projRes PH) (FibRep n) 3 hU3)
  have h1 : Function.Bijective ((groupHomologyZIsoR U (RG_projRes PH) (FibRep n) 3).inv.hom) :=
    ConcreteCategory.bijective_of_isIso (groupHomologyZIsoR U (RG_projRes PH) (FibRep n) 3).inv
  exact h1.2.comp hbij.2

/-- The linear form `x ↦ lin(ι_M(evalQ x))` on the kernel `K_M`, the coefficient at the standard edge. -/
def treeEv (T : TreeData) (n : ℕ) : KMT T n →ₗ[ℚ] BinaryV (n + 1) :=
  (fiberLin n).toLinearMap ∘ₗ (iotaM U (FibRep n) T.ℓ₀ T.hℓ) ∘ₗ
    (evalQ pibar hker_pibar (Abar U (FibRep n) ⊗ T.L)) ∘ₗ
      (KM (Rep.res pibar P1) (Rep.res pibar P0) (Rep.resMap pibar d1) (Abar U (FibRep n) ⊗ T.L)).subtype

theorem tree_chain (T : TreeData) (n : ℕ) (x : KMT T n) :
    Cmap n (((trY PN (YAR (RG_projRes PH) (FibRep n))).f 3).hom
        (lamChain U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) T.t3 x)) =
      (2 * (Fintype.card (PH ⧸ PN) : ℚ)⁻¹) • iotaM U (FibRep n) T.ℓ₀ T.hℓ
        (evalQ pibar hker_pibar (Abar U (FibRep n) ⊗ T.L) x.1) := by
  obtain ⟨S, hS⟩ := exists_stab_finset
  obtain ⟨m, hm⟩ := exists_mk_edgeGen pibar pibar_surjective (Abar U (FibRep n) ⊗ T.L) x.1
  obtain ⟨a, rfl⟩ := one_dim_tmul T.ℓ₀ T.hℓ T.hL m
  have hlc : lamChain U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) T.t3 x =
      Coinvariants.mk ((YAR (RG_projRes PH) (FibRep n)).X 3).ρ (a ⊗ₜ[ℚ] genT0) := by
    unfold lamChain
    rw [hm]
    exact ZIsoR_Lam_mk U (FibRep n) (RG_projRes PH) T.t3 a T.ℓ₀ edgeGen genT0 T.ht3
  rw [hlc]
  refine (T3_chain n a S hS).trans ?_
  rw [hm]
  let _ : MulAction (PH ⧸ U) OTE := oteMulActionQ pibar
  rw [stab_sum_eq n a S hS _ _ (mem_transp_p0 U pibar hker_pibar) (mem_transp_swap U pibar hker_pibar),
    iotaM_evalQ_edgeGen_explicit U (FibRep n) pibar hker_pibar T.ℓ₀ T.hℓ _ (hL_char T) a _ _
      (mem_transp_p0 U pibar hker_pibar) (mem_transp_swap U pibar hker_pibar)]
  rw [smul_smul]
  congr 1
  ring

theorem tree_cell (T : TreeData) (n : ℕ) :
    ∃ c₂ : ℚ, c₂ ≠ 0 ∧ ∀ (w : groupHomology (Rep.res PN.subtype (FibRep n)) 3), avgN PN (FibRep n) 3 w = w →
      ∀ x : KMT T n, treeY T n x = corN PN (FibRep n) 3 w → FidL n w = c₂ • treeEv T n x := by
  obtain ⟨cB, hcB, hFid⟩ := FidL_eq_coeff
  have hcard : (Fintype.card (PH ⧸ PN) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := PH ⧸ PN)).ne'
  refine ⟨cB * (2 * (Fintype.card (PH ⧸ PN) : ℚ)⁻¹), mul_ne_zero hcB (mul_ne_zero two_ne_zero (inv_ne_zero hcard)),
    fun w hw x hx => ?_⟩
  obtain ⟨ζ, hζ, hcl⟩ := exists_cycleClass (CxN PN (YAR (RG_projRes PH) (FibRep n)))
    ((eNR PN (RG_projRes PH) (FibRep n) 3).hom.hom w)
  have h4N := CxN_d_four PN (FibRep n) (RG_projRes PH) (RG_projRes_d_four PH)
  have h4K := CxK_d_four (FibRep n) (RG_projRes PH) (RG_projRes_d_four PH)
  obtain ⟨hav, hζtr, hz', hclK⟩ := invariant_of_avgN_fixed PN (RG_projRes PH) (FibRep n) h4N w hw ζ hζ hcl
  have hlam := eKR_inv_LamH U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) T.t3 T.t2 T.hi x
  have hq : ((QY PN (YAR (RG_projRes PH) (FibRep n))).f 3).hom ζ =
      lamChain U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) T.t3 x := by
    refine cycleClass_injective_top (CxK (YAR (RG_projRes PH) (FibRep n))) h4K _ _ hz'
      (lamChain_cycle U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) T.t3 T.t2 T.hi x) ?_
    rw [hclK, ← hx]
    exact hlam
  have hζ' : ζ = ((trY PN (YAR (RG_projRes PH) (FibRep n))).f 3).hom
      (lamChain U (FibRep n) (RG_projRes PH) (Rep.resMap pibar d1) T.t3 x) := by
    rw [← hq]
    exact hζtr
  have hz := pushRG_cycle n ζ hζ
  have hzw := pushRG_iotaStar n w ζ hζ hcl
  rw [hFid n w _ hz hzw]
  have hC' := tree_chain T n x
  rw [← hζ'] at hC'
  change cB • literalFiberMap n 0 (Cmap n ζ) = _
  rw [hC', map_smul, smul_smul]
  rfl

theorem faceEvalAvg_of_tree (T : TreeData) (n : ℕ) : FaceEvalAvg n := by
  obtain ⟨c₁, hc₁, hκ⟩ := tree_kappa T n
  obtain ⟨c₂, hc₂, hcell⟩ := tree_cell T n
  refine faceEvalAvg_of_data n (treeY T n) (treeY_surjective T n) (treeEv T n) c₁ c₂ hc₁ hc₂ ?_ hcell
  intro x
  exact periodEquiv_edge2 (n + 1) (kappaLit n (treeY T n x)) _ c₁ (hκ x)

/-- **Lemma B.1, the literal residue comparison, from the tree data**: `PHCompat n` for every `n`. -/
theorem phCompat_of_tree (T : TreeData) (n : ℕ) : PHCompat n :=
  (phCompat_iff_faceEvalAvg' n).mpr (faceEvalAvg_of_tree T n)

end TernaryPeriodPolynomials.Argument.AppendixBResidue
