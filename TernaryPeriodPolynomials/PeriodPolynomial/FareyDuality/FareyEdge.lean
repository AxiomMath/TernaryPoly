module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FareyResolution
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.PermEval

@[expose] public section


/-!
# The standard-edge coefficient of `H₁(GL₂(ℤ), M)`

Formalized by Claude Sonnet 5.5.

For every `ℚ`-representation `M` of `Γ = GL₂(ℤ)`:

* `H1Iso M`: `H₁(Γ, M)` (Mathlib's `groupHomology`) is the kernel of the boundary
  `dC M : (M ⊗ P1)_Γ → (M ⊗ P0)_Γ` of the dual Farey tree.
* `edge2 M : H₁(Γ, M) → M` reads the coefficient of the standard oriented edge `p0 = (triPlus, triMinus)` of a cycle
  (evaluation at the base point of the norm isomorphism `(M ⊗ ℚ[OTE])_Γ ≅ M^{Stab p0}`).
* `edge2_injective`, `edge2_isEdgeCoeff` and `edge2_surjective_of`: `edge2 M` is a linear isomorphism of `H₁(Γ, M)` onto
  `{b ∈ M | b is Stab(p0)-invariant, sOne · b = -b, ∑_{σ ∈ Stab(triPlus)} σ b = 0}` (`IsEdgeCoeff`), where
  `sOne = diag(1, -1)` exchanges the two triangles over the standard edge.  These are the period relations of the
  standard well-rounded binary edge.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FareyTree

open CategoryTheory CategoryTheory.Limits Representation Rep TernaryPoly.RankTwoAugmentedFrames
open scoped Classical

/-- The boundary on coinvariants: `(M ⊗ P1)_Γ → (M ⊗ P0)_Γ`. -/
def dC (M : Rep ℚ IntegralGL) :
    ((Rep.coinvariantsTensor ℚ IntegralGL).obj M).obj P1 ⟶ ((Rep.coinvariantsTensor ℚ IntegralGL).obj M).obj P0 :=
  ((Rep.coinvariantsTensor ℚ IntegralGL).obj M).map d1

/-- `H₁(GL₂(ℤ), M)` is the kernel of the boundary on coinvariants of the dual Farey tree. -/
def H1Iso (M : Rep ℚ IntegralGL) :
    groupHomology M 1 ≅ ModuleCat.of ℚ (LinearMap.ker (dC M).hom) := by
  refine groupHomologyFarey M 1 ≪≫ ?_
  refine (HomologicalComplex.homologyIsoSc' _ 2 1 0 (by simp) (by simp)) ≪≫ ?_
  set S := HomologicalComplex.sc' (farResolution.complex.coinvariantsTensorObj M) 2 1 0 with hS
  have hf : S.f = 0 := by
    change ((Rep.coinvariantsTensor ℚ IntegralGL).obj M).map (farComplex.d 2 1) = 0
    have : farComplex.d 2 1 = 0 := ChainComplex.of_d farX farD 1
    rw [this, Functor.map_zero]
  haveI := ShortComplex.isIso_homologyπ S hf
  have hg : S.g = dC M := by
    change ((Rep.coinvariantsTensor ℚ IntegralGL).obj M).map (farComplex.d 1 0) = _
    rw [show farComplex.d 1 0 = d1 from ChainComplex.of_d farX farD 0]
    rfl
  refine (asIso S.homologyπ).symm ≪≫ S.moduleCatCyclesIso ≪≫ ?_
  have e : S.moduleCatLeftHomologyData.K = ModuleCat.of ℚ ↥(LinearMap.ker (dC M).hom) := by
    change ModuleCat.of ℚ (LinearMap.ker S.g.hom) = _
    rw [hg]
    rfl
  exact eqToIso e


/-- The diagonal matrix `diag(1, -1)`, which exchanges the two triangles over the standard edge. -/
def sOne : IntegralGL := colGL e1 (-e2) e12_unimod.neg_right

theorem colGL_val_zero (a b : IntegralVector) (hd) (i : Fin 2) : (colGL a b hd).val i 0 = a i := by
  fin_cases i <;> rfl

theorem colGL_val_one (a b : IntegralVector) (hd) (i : Fin 2) : (colGL a b hd).val i 1 = b i := by
  fin_cases i <;> rfl

theorem colGL_e1_e2 : colGL e1 e2 e12_unimod = 1 := by
  apply Units.ext
  ext i j
  fin_cases j <;> fin_cases i <;> simp [colGL_val_zero, colGL_val_one, e1, e2]

theorem triPlus_val : triPlus.1 = augmentedFrame (1 : IntegralGL) := by
  have := frame_plus isGen_cusp1 isGen_cusp2 e12_unimod
  rw [colGL_e1_e2] at this
  exact this

theorem triMinus_val : triMinus.1 = augmentedFrame sOne := frame_minus_eq isGen_cusp1 isGen_cusp2 e12_unimod

theorem sOne_mul_self : sOne * sOne = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sOne, Matrix.mul_apply, Fin.sum_univ_two, colGL_val_zero, colGL_val_one, e1, e2]

theorem sOne_smul_triPlus : sOne • triPlus = triMinus := by
  apply Subtype.ext
  rw [tri_smul_val, triPlus_val, smul_frame, mul_one, triMinus_val]

theorem sOne_smul_triMinus : sOne • triMinus = triPlus := by
  rw [← sOne_smul_triPlus, ← mul_smul, sOne_mul_self, one_smul]

/-- The standard oriented edge from `triPlus` to `triMinus`. -/
def p0 : OTE := oteOf triPlus triMinus tAdj_triPlus_triMinus

theorem sOne_smul_p0 : sOne • p0 = p0.swap := by
  apply Subtype.ext
  show (sOne • triPlus, sOne • triMinus) = (triMinus, triPlus)
  rw [sOne_smul_triPlus, sOne_smul_triMinus]

theorem tri_over_standard_edge {t : Tri} (h1 : cusp1 ∈ t.1) (h2 : cusp2 ∈ t.1) :
    t = triPlus ∨ t = triMinus := by
  obtain ⟨z, hz, hz1, hz2, htz⟩ := tri_third h1 h2 cusp1_ne_cusp2
  rcases tri_third_cases h1 h2 hz hz1 hz2 isGen_cusp1 isGen_cusp2 e12_unimod with e | e
  · left; apply Subtype.ext; rw [htz, e]; rfl
  · right; apply Subtype.ext; rw [htz, e]; rfl

theorem ote_transitive (p : OTE) : ∃ g : IntegralGL, g • p0 = p := by
  obtain ⟨⟨t, t'⟩, hadj⟩ := p
  obtain ⟨hne, x, y, hxy, hx, hy, hx', hy'⟩ := hadj
  have hadj_xy : Adj x y := tri_adj hx hy hxy
  obtain ⟨g, hg0, hg1⟩ := edge_basis x y hadj_xy.1 hadj_xy.2
  have c1 : g • cusp1 = x := by rw [smul_cusp1, hg0]
  have c2 : g • cusp2 = y := by rw [smul_cusp2, hg1]
  have mem : ∀ {s : Tri}, x ∈ s.1 → y ∈ s.1 → g⁻¹ • s = triPlus ∨ g⁻¹ • s = triMinus := by
    intro s hxs hys
    apply tri_over_standard_edge
    · rw [mem_tri_smul, inv_inv, c1]; exact hxs
    · rw [mem_tri_smul, inv_inv, c2]; exact hys
  have hne' : g⁻¹ • t ≠ g⁻¹ • t' := fun e => hne (MulAction.injective g⁻¹ e)
  rcases mem hx hy with ht | ht <;> rcases mem hx' hy' with ht' | ht'
  · exact absurd (ht.trans ht'.symm) hne'
  · refine ⟨g, Subtype.ext (Prod.ext ?_ ?_)⟩
    · show g • triPlus = t
      rw [← ht, smul_inv_smul]
    · show g • triMinus = t'
      rw [← ht', smul_inv_smul]
  · refine ⟨g * sOne, Subtype.ext (Prod.ext ?_ ?_)⟩
    · show (g * sOne) • triPlus = t
      rw [mul_smul, sOne_smul_triPlus, ← ht, smul_inv_smul]
    · show (g * sOne) • triMinus = t'
      rw [mul_smul, sOne_smul_triMinus, ← ht', smul_inv_smul]
  · exact absurd (ht.trans ht'.symm) hne'

theorem tri_transitive (t : Tri) : ∃ g : IntegralGL, g • triPlus = t :=
  (exists_smul_triPlus t).imp fun _ h => h.symm

section Edge

open TernaryPeriodPolynomials.Argument.BinaryDuality

variable (M : Rep ℚ IntegralGL)

/-- Coinvariants `(M ⊗ P)_Γ`. -/
abbrev CT (P : Rep ℚ IntegralGL) : ModuleCat ℚ := ((Rep.coinvariantsTensor ℚ IntegralGL).obj M).obj P

theorem CT_map_mk {P Q : Rep ℚ IntegralGL} (f : P ⟶ Q) (m : M) (p : P) :
    (((Rep.coinvariantsTensor ℚ IntegralGL).obj M).map f).hom (Coinvariants.mk _ (m ⊗ₜ p)) =
      Coinvariants.mk _ (m ⊗ₜ f.hom p) := rfl

/-- Evaluation at the standard oriented edge. -/
def evalP : CT M PE →ₗ[ℚ] M := evalAt (ote_stabilizer_finite p0) M

/-- Evaluation at the standard triangle. -/
def evalT : CT M P0 →ₗ[ℚ] M := evalAt (tri_stabilizer_finite triPlus) M

theorem ote_htr : ∀ y : OTE, ∃ γ : IntegralGL, γ • p0 = y := ote_transitive

theorem tri_htr : ∀ y : Tri, ∃ γ : IntegralGL, γ • triPlus = y := tri_transitive

/-- Generators `m ↦ [m ⊗ p₀]` of `(M ⊗ PE)_Γ`. -/
abbrev genP : M →ₗ[ℚ] CT M PE := genAt (x₀ := p0) M

/-- Generators `m ↦ [m ⊗ t₊]` of `(M ⊗ P0)_Γ`. -/
abbrev genT : M →ₗ[ℚ] CT M P0 := genAt (x₀ := triPlus) M

theorem evalP_injective : Function.Injective (evalP M) :=
  evalAt_injective (ote_stabilizer_finite p0) M ote_htr

theorem evalT_injective : Function.Injective (evalT M) :=
  evalAt_injective (tri_stabilizer_finite triPlus) M tri_htr

theorem sOne_inv : sOne⁻¹ = sOne := inv_eq_of_mul_eq_one_right sOne_mul_self

/-- The swap involution on `(M ⊗ PE)_Γ`. -/
def sigC : CT M PE ⟶ CT M PE := ((Rep.coinvariantsTensor ℚ IntegralGL).obj M).map swapMap

theorem sigC_genP (m : M) : (sigC M).hom (genP M m) = genP M (M.ρ sOne m) := by
  have h : (sigC M).hom (genP M m) =
      Coinvariants.mk _ (m ⊗ₜ swapMap.hom (MonoidAlgebra.single p0 (1 : ℚ))) := rfl
  rw [h, swapMap_single, ← sOne_smul_p0]
  have h2 : genP M (M.ρ sOne m) = Coinvariants.mk _ ((M.ρ sOne m) ⊗ₜ MonoidAlgebra.single p0 (1 : ℚ)) := rfl
  rw [h2]
  have key := Coinvariants.mk_inv_tmul (ρ := M.ρ) (τ := (Rep.ofMulAction ℚ IntegralGL OTE).ρ)
    m (MonoidAlgebra.single p0 (1 : ℚ)) sOne
  rw [sOne_inv, Representation.ofMulAction_single] at key
  exact key.symm

theorem stab_p0_conj (γ : IntegralGL) :
    γ ∈ MulAction.stabilizer IntegralGL p0 ↔ sOne⁻¹ * γ * sOne ∈ MulAction.stabilizer IntegralGL p0 := by
  simp only [MulAction.mem_stabilizer_iff]
  have key : (sOne⁻¹ * γ * sOne) • p0 = sOne⁻¹ • (γ • p0).swap := by
    rw [mul_smul, mul_smul, sOne_smul_p0, OTE.swap_smul]
  rw [key]
  constructor
  · intro h
    rw [h, ← sOne_smul_p0, inv_smul_smul]
  · intro h
    rw [inv_smul_eq_iff, sOne_smul_p0] at h
    have := congrArg OTE.swap h
    simpa using this

theorem normStab_p_sOne (m : M) :
    normStab (ote_stabilizer_finite p0) M (M.ρ sOne m) =
      M.ρ sOne (normStab (ote_stabilizer_finite p0) M m) := by
  apply normStab_conj
  intro γ
  rw [← sOne_inv]
  simpa [sOne_inv] using stab_p0_conj γ

theorem evalP_genP (m : M) : evalP M (genP M m) = normStab (ote_stabilizer_finite p0) M m :=
  evalAt_genAt (ote_stabilizer_finite p0) M m

theorem evalP_sigC (w : CT M PE) : evalP M ((sigC M).hom w) = M.ρ sOne (evalP M w) := by
  obtain ⟨m, rfl⟩ := genAt_surjective (x₀ := p0) M ote_htr w
  rw [sigC_genP, evalP_genP, evalP_genP, normStab_p_sOne]

/-- The boundary on `(M ⊗ PE)_Γ`. -/
def dW : CT M PE ⟶ CT M P0 := ((Rep.coinvariantsTensor ℚ IntegralGL).obj M).map dTilde

theorem evalT_dW_genP (m : M) :
    evalT M ((dW M).hom (genP M m)) =
      normStab (tri_stabilizer_finite triPlus) M (M.ρ sOne m) -
        normStab (tri_stabilizer_finite triPlus) M m := by
  have h : (dW M).hom (genP M m) = Coinvariants.mk _ (m ⊗ₜ dTilde.hom (MonoidAlgebra.single p0 (1 : ℚ))) := rfl
  rw [h, dTilde_single]
  change evalTen (tri_stabilizer_finite triPlus) M
    (m ⊗ₜ (MonoidAlgebra.single p0.1.2 (1 : ℚ) - MonoidAlgebra.single p0.1.1 (1 : ℚ))) = _
  rw [TensorProduct.tmul_sub, map_sub, evalTen_tmul_single, evalTen_tmul_single, one_smul, one_smul]
  have e1 : p0.1.2 = sOne • triPlus := sOne_smul_triPlus.symm
  have e0 : p0.1.1 = triPlus := rfl
  rw [e1, e0, normAt_smul_base, sOne_inv]
  rfl

theorem inclP1_swap : inclP1 ≫ swapMap = -inclP1 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  have h := mem_antiSub.mp c.2
  change swapMap.hom (c : PE) = -(c : PE)
  exact eq_neg_of_add_eq_zero_left h

theorem retrP1_inclP1 : retrP1 ≫ inclP1 = (1 / 2 : ℚ) • (𝟙 PE - swapMap) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  change antiLin c = (1 / 2 : ℚ) • (c - swapMap.hom c)
  rfl

/-- Inclusion of the antisymmetric part. -/
def inclC : CT M P1 ⟶ CT M PE := ((Rep.coinvariantsTensor ℚ IntegralGL).obj M).map inclP1

/-- Antisymmetrization. -/
def retrC : CT M PE ⟶ CT M P1 := ((Rep.coinvariantsTensor ℚ IntegralGL).obj M).map retrP1

theorem inclC_retrC : inclC M ≫ retrC M = 𝟙 _ := by
  unfold inclC retrC
  rw [← Functor.map_comp, inclP1_retrP1, CategoryTheory.Functor.map_id]

theorem inclC_injective : Function.Injective (inclC M).hom := by
  intro a b h
  have := congrArg (fun f => (retrC M).hom f) h
  have e : ∀ x, (retrC M).hom ((inclC M).hom x) = x := fun x =>
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (inclC_retrC M)) x
  simpa [e] using this

theorem inclC_sigC : inclC M ≫ sigC M = -inclC M := by
  unfold inclC sigC
  rw [← Functor.map_comp, inclP1_swap, Functor.map_neg]

theorem retrC_inclC : retrC M ≫ inclC M = (1 / 2 : ℚ) • (𝟙 _ - sigC M) := by
  unfold inclC retrC sigC
  rw [← Functor.map_comp, retrP1_inclP1, Functor.map_smul, Functor.map_sub, CategoryTheory.Functor.map_id]

theorem dC_eq : dC M = inclC M ≫ dW M := by
  unfold dC inclC dW d1
  rw [Functor.map_comp]

/-- The number of elements of the stabilizer of the standard oriented edge. -/
def nP : ℕ := (transp_finite (ote_stabilizer_finite p0) p0).toFinset.card

theorem nP_pos : (nP : ℚ) ≠ 0 := by
  have : nP ≠ 0 := by
    apply Finset.card_ne_zero_of_mem (a := 1)
    rw [Set.Finite.mem_toFinset, transp_base]
    exact (MulAction.stabilizer IntegralGL p0).one_mem
  exact_mod_cast this

theorem nP_smul_eq (w : CT M PE) : (nP : ℚ) • w = genP M (evalP M w) := by
  obtain ⟨m, rfl⟩ := genAt_surjective (x₀ := p0) M ote_htr w
  have := card_smul_genAt (ote_stabilizer_finite p0) M m
  rw [← Nat.cast_smul_eq_nsmul ℚ] at this
  rw [evalP_genP]
  exact this

/-- The coefficient at the standard oriented edge of a class in `H₁(GL₂(ℤ), M)`. -/
def edge2 : groupHomology M 1 →ₗ[ℚ] M :=
  evalP M ∘ₗ (inclC M).hom ∘ₗ (LinearMap.ker (dC M).hom).subtype ∘ₗ (H1Iso M).hom.hom

/-- The conditions satisfied by the standard-edge coefficient of a homology class: invariant under the
stabilizer of the oriented edge, odd under the swap of the two triangles, annihilated by the norm over the
triangle stabilizer. -/
structure IsEdgeCoeff (b : M) : Prop where
  stab : ∀ s : MulAction.stabilizer IntegralGL p0, M.ρ s b = b
  anti : M.ρ sOne b = -b
  cycle : normStab (tri_stabilizer_finite triPlus) M b = 0

theorem edge2_injective : Function.Injective (edge2 M) := by
  intro x y h
  have h1 := evalP_injective M h
  have h2 := inclC_injective M h1
  have h3 := Subtype.ext h2
  exact (ModuleCat.mono_iff_injective (H1Iso M).hom).mp inferInstance h3

theorem evalT_dW_genP_anti (b : M) (hb : M.ρ sOne b = -b) :
    evalT M ((dW M).hom (genP M b)) = (-2 : ℚ) • normStab (tri_stabilizer_finite triPlus) M b := by
  rw [evalT_dW_genP, hb, map_neg]
  module

theorem edge2_isEdgeCoeff (x : groupHomology M 1) : IsEdgeCoeff M (edge2 M x) := by
  set z := (H1Iso M).hom.hom x with hz
  set w := (inclC M).hom (z : CT M P1) with hw
  have hb : edge2 M x = evalP M w := rfl
  have hcyc : (dW M).hom w = 0 := by
    have := z.2
    rw [LinearMap.mem_ker] at this
    have e := congrArg (fun f : CT M P1 ⟶ CT M P0 => f.hom (z : CT M P1)) (dC_eq M)
    exact e.symm.trans this
  have hanti : (sigC M).hom w = -w := by
    have := congrArg (fun f => f.hom (z : CT M P1)) (inclC_sigC M)
    simpa using this
  have hstab : ∀ s : MulAction.stabilizer IntegralGL p0, M.ρ s (evalP M w) = evalP M w :=
    (mem_range_evalAt (ote_stabilizer_finite p0) M ote_htr (evalP M w)).mp ⟨w, rfl⟩
  have hanti' : M.ρ sOne (evalP M w) = -evalP M w := by
    rw [← evalP_sigC, hanti, map_neg]
  refine ⟨hb ▸ hstab, hb ▸ hanti', ?_⟩
  rw [hb]
  have hn := nP_smul_eq M w
  have h1 : evalT M ((dW M).hom ((nP : ℚ) • w)) = 0 := by rw [map_smul, hcyc, smul_zero, map_zero]
  rw [hn, evalT_dW_genP_anti M _ hanti'] at h1
  exact (smul_eq_zero.mp h1).resolve_left (by norm_num)

theorem normStab_p_of_inv (b : M) (hb : ∀ s : MulAction.stabilizer IntegralGL p0, M.ρ s b = b) :
    normStab (ote_stabilizer_finite p0) M b = (nP : ℚ) • b := by
  unfold normStab normAt
  rw [LinearMap.sum_apply]
  have : ∀ γ ∈ (transp_finite (ote_stabilizer_finite p0) p0).toFinset, M.ρ γ b = b := by
    intro γ hγ
    have hγ' : γ ∈ MulAction.stabilizer IntegralGL p0 := by
      have := (Set.Finite.mem_toFinset _).mp hγ
      rw [transp_base] at this
      exact this
    exact hb ⟨γ, hγ'⟩
  rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  rfl

theorem edge2_surjective_of {b : M} (hb : IsEdgeCoeff M b) : ∃ x, edge2 M x = b := by
  set w : CT M PE := (nP : ℚ)⁻¹ • genP M b with hw
  have hsig : (sigC M).hom w = -w := by
    rw [hw, map_smul, sigC_genP, hb.anti, map_neg, smul_neg]
  set z0 : CT M P1 := (retrC M).hom w with hz0
  have hinc : (inclC M).hom z0 = w := by
    have := congrArg (fun f => f.hom w) (retrC_inclC M)
    simp only [ModuleCat.hom_comp] at this
    change (inclC M).hom ((retrC M).hom w) = _ at this
    rw [this]
    have h2 : ((1 / 2 : ℚ) • (𝟙 (CT M PE) - sigC M)).hom w = (1 / 2 : ℚ) • (w - (sigC M).hom w) := rfl
    rw [h2, hsig]
    module
  have hdW : (dW M).hom w = 0 := by
    apply evalT_injective M
    rw [map_zero, hw, map_smul, map_smul, evalT_dW_genP_anti M b hb.anti, hb.cycle]
    simp
  have hker : z0 ∈ LinearMap.ker (dC M).hom := by
    rw [LinearMap.mem_ker]
    have e := congrArg (fun f : CT M P1 ⟶ CT M P0 => f.hom z0) (dC_eq M)
    exact e.trans (by simp only [ModuleCat.hom_comp, LinearMap.comp_apply]; change (dW M).hom ((inclC M).hom z0) = 0; rw [hinc]; exact hdW)
  refine ⟨(H1Iso M).inv.hom ⟨z0, hker⟩, ?_⟩
  have hinv : (H1Iso M).hom.hom ((H1Iso M).inv.hom ⟨z0, hker⟩) = ⟨z0, hker⟩ :=
    Iso.inv_hom_id_apply (H1Iso M) _
  show evalP M ((inclC M).hom ((H1Iso M).hom.hom ((H1Iso M).inv.hom ⟨z0, hker⟩))) = b
  rw [hinv]
  show evalP M ((inclC M).hom z0) = b
  rw [hinc, hw, map_smul, evalP_genP, normStab_p_of_inv M b hb.stab, smul_smul, inv_mul_cancel₀ nP_pos, one_smul]

end Edge

end TernaryPeriodPolynomials.Argument.FareyTree
