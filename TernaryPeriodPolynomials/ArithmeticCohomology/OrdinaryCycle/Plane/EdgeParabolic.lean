module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SymbolRestriction

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.OrdinaryPlaneEdge
open OrdinaryResidueParabolic

/-- A rational block parabolic acts on embedded plane vectors only through its binary block. -/
theorem parabolic_vectorAction_embed (g : OrdinaryFullAction.GL3) (lam : ℚˣ) (u : Fin 2 → ℚ)
    (C : BinaryModularSymbol.GL2) (hg : g.val = blockMatrix lam u C) (x : Fin 2 → ℚ) :
    OrdinaryFullAction.vectorAction g (embed x) = embed (BinaryModularSymbol.vectorAction C x) := by
  change g.val.mulVec (embed x) = embed (C.val.mulVec x)
  rw [hg]
  ext i
  fin_cases i <;> simp [blockMatrix,embed,Matrix.mulVec,dotProduct,Fin.sum_univ_three,Fin.sum_univ_two]

theorem parabolic_lineAction_embedLine (g : OrdinaryFullAction.GL3) (lam : ℚˣ) (u : Fin 2 → ℚ)
    (C : BinaryModularSymbol.GL2) (hg : g.val = blockMatrix lam u C) (L : BinaryModularSymbol.Line) :
    OrdinaryFullAction.lineAction g (embedLine L).val =
      (embedLine (BinaryModularSymbol.lineAction C L)).val := by
  apply Subtype.ext
  change (L.val.map embed).map (OrdinaryFullAction.vectorAction g).toLinearMap =
    (L.val.map (BinaryModularSymbol.vectorAction C).toLinearMap).map embed
  rw [←Submodule.map_comp,←Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact parabolic_vectorAction_embed g lam u C hg x

/-- The image of the exterior line remains outside the plane, since lambda is a unit. -/
theorem parabolic_exterior_outside (g : OrdinaryFullAction.GL3) (lam : ℚˣ) (u : Fin 2 → ℚ)
    (C : BinaryModularSymbol.GL2) (hg : g.val = blockMatrix lam u C) :
    ¬(OrdinaryFullAction.lineAction g exterior).val ≤ planeZero.val := by
  intro h
  have hm : OrdinaryFullAction.vectorAction g (![1,0,0] : Fin 3 → ℚ) ∈
      (OrdinaryFullAction.lineAction g exterior).val :=
    ⟨![1,0,0],Submodule.subset_span (Set.mem_singleton _),rfl⟩
  have he := (mem_planeZero _).mp (h hm)
  change (g.val.mulVec ![1,0,0]) 0 = 0 at he
  rw [hg] at he
  simp [blockMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three,Units.ne_zero lam] at he

/-- Projecting the actual parabolic image of a coned symbol gives precisely its binary image. -/
theorem binaryProject_action_binaryCone (g : OrdinaryFullAction.GL3) (lam : ℚˣ) (u : Fin 2 → ℚ)
    (C : BinaryModularSymbol.GL2) (hg : g.val = blockMatrix lam u C) (c : BinaryModularSymbol.St) :
    binaryProject (OrdinaryFullAction.cycleAction g (binaryCone c)) = BinaryModularSymbol.action C c := by
  have hc : c ∈ Submodule.span ℚ (Set.range (BinaryModularSymbol.symbol
      (RankTwoAugmentedFrames.augmentedLine 1 0))) := by
    rw [BinaryModularSymbol.span_symbols]
    trivial
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨L,rfl⟩ := hc
    rw [binaryCone_symbol,cycleAction_apartment,
      parabolic_lineAction_embedLine g lam u C hg,parabolic_lineAction_embedLine g lam u C hg]
    change symbolEquiv.symm (project planeZero (GoodApartmentCycles.apartmentCycle (fun _ => True)
      (OrdinaryFullAction.lineAction g exterior) _ _)) = _
    rw [project_apartment planeZero _ (parabolic_exterior_outside g lam u C hg),
      ←symbolEquiv_symbol,LinearEquiv.symm_apply_apply,BinaryModularSymbol.action_symbol]
  | zero => simp only [map_zero]
  | add c d _ _ hc hd => simp only [map_add,hc,hd]
  | smul q c _ hc => simp only [map_smul,hc]

/-- The actual integral matrix contains a genuine integral invertible Levi block whenever its first row is parabolic. -/
theorem integral_block_decomposition (g : ModThreeGoodAction.IntegralGL)
    (h1 : g.val 0 1 = 0) (h2 : g.val 0 2 = 0) :
    ∃ C : RankTwoAugmentedFrames.IntegralGL, ∃ lam : ℚˣ, ∃ u : Fin 2 → ℚ,
      (OrdinaryFullAction.integral g).val = blockMatrix lam u (BinaryModularSymbol.integral C) := by
  let M : Matrix (Fin 2) (Fin 2) ℤ := fun i j => g.val i.succ j.succ
  have hd : g.val.det = g.val 0 0 * M.det := by
    rw [Matrix.det_fin_three,Matrix.det_fin_two]
    simp only [M,h1,h2,zero_mul,add_zero,sub_zero]
    change g.val 0 0 * g.val 1 1 * g.val 2 2 - g.val 0 0 * g.val 1 2 * g.val 2 1 =
      g.val 0 0 * (g.val 1 1 * g.val 2 2 - g.val 1 2 * g.val 2 1)
    ring
  have hu : IsUnit (g.val 0 0 * M.det) := hd ▸ (Matrix.GeneralLinearGroup.det g).isUnit
  have hl := (IsUnit.mul_iff.mp hu).1
  have hC := (IsUnit.mul_iff.mp hu).2
  let C : RankTwoAugmentedFrames.IntegralGL := Matrix.nonsingInvUnit M hC
  let lam : ℚˣ := Units.map (Int.castRingHom ℚ) hl.unit
  refine ⟨C,lam,fun i => (g.val i.succ 0 : ℚ),?_⟩
  have hlam : (lam : ℚ) = (g.val 0 0 : ℚ) := by
    change ((hl.unit : ℤ) : ℚ) = _
    rw [hl.unit_spec]
  have hCi : (BinaryModularSymbol.integral C).val = M.map (Int.castRingHom ℚ) := rfl
  change g.val.map (Int.castRingHom ℚ) = _
  unfold blockMatrix
  rw [hCi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M,hlam,h1,h2] <;> rfl

end TernaryPoly.OrdinaryPlaneEdge
