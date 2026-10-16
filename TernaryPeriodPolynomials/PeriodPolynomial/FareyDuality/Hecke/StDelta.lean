module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FarePeriod
public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Hom

@[expose] public section


/-!
# The determinant-twisted Steinberg module and the symbol map on oriented dual edges

Formalized by Claude Sonnet 5.5.

* `StD`: the Steinberg module `St` (kernel of the augmentation of finite divisors on the cusps) with the action
  `γ • σ = det γ · (γ σ)` of `GL₂(ℤ)` (`stD`).
* `permLift`: a `Γ`-map out of a permutation module with prescribed equivariant values on the basis.
* `edgeSym q`: the symbol of an oriented edge of the dual Farey tree, defined by transitivity from
  `edgeSym p0 = reference` (the stabilizer of `p0` fixes the reference symbol up to the determinant sign,
  `stD_stab_reference`); `edgeSym_swap`: reversing the edge negates it.
* `piT : ℚ[OTE] ⟶ StD`: the resulting symbol map, surjective by the library's integral generation of `St`
  (`piT_surjective`).  Its kernel is computed in `FareyChains`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeDuality

open CategoryTheory TernaryPoly TernaryPoly.BinaryModularSymbol TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.FareyTree
open scoped MonoidAlgebra Classical

/-- A `Γ`-map out of a permutation module with prescribed (equivariant) values on the basis. -/
def permLift {Γ : Type} [Group Γ] {X : Type} [MulAction Γ X] (M : Rep ℚ Γ) (F : X → M)
    (hF : ∀ (g : Γ) (x : X), F (g • x) = M.ρ g (F x)) :
    Rep.ofMulAction ℚ Γ X ⟶ M :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (Rep.ofMulAction ℚ Γ X).ρ) (σ := M.ρ)
    (Finsupp.linearCombination ℚ F ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
    (fun g v => by
      have key : (Finsupp.linearCombination ℚ F ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) ∘ₗ
            (Representation.ofMulAction ℚ Γ X g) =
          (M.ρ g) ∘ₗ (Finsupp.linearCombination ℚ F ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) := by
        refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
        simp [Representation.ofMulAction_single, hF]
      exact LinearMap.congr_fun key v))

theorem permLift_single {Γ : Type} [Group Γ] {X : Type} [MulAction Γ X] (M : Rep ℚ Γ) (F : X → M)
    (hF : ∀ (g : Γ) (x : X), F (g • x) = M.ρ g (F x)) (x : X) (r : ℚ) :
    (permLift M F hF).hom (MonoidAlgebra.single x r) = r • F x := by
  simp [permLift]

/-- The determinant of an integral matrix as a rational number (`±1`). -/
def detQ : IntegralGL →* ℚ where
  toFun g := (((Matrix.GeneralLinearGroup.det g : ℤˣ) : ℤ) : ℚ)
  map_one' := by simp
  map_mul' g h := by simp [map_mul]

theorem detQ_mul_self (g : IntegralGL) : detQ g * detQ g = 1 := by
  have h : (((Matrix.GeneralLinearGroup.det g : ℤˣ) : ℤ)) * ((Matrix.GeneralLinearGroup.det g : ℤˣ) : ℤ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self]; rfl
  change (((Matrix.GeneralLinearGroup.det g : ℤˣ) : ℤ) : ℚ) * (((Matrix.GeneralLinearGroup.det g : ℤˣ) : ℤ) : ℚ) = 1
  exact_mod_cast h


theorem detQ_eq (g : IntegralGL) :
    detQ g = ((g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 : ℤ) : ℚ) := by
  simp [detQ, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

/-- The `GL₂(ℤ)`-action on the Steinberg module twisted by the determinant sign. -/
def stD : Representation ℚ IntegralGL St where
  toFun g := detQ g • action (integral g)
  map_one' := by simp
  map_mul' g h := by
    apply LinearMap.ext
    intro σ
    simp only [map_mul, LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul, mul_comm (detQ g)]

/-- The determinant-twisted Steinberg representation. -/
abbrev StD : Rep ℚ IntegralGL := Rep.of stD

theorem stD_apply (g : IntegralGL) (σ : St) : stD g σ = detQ g • action (integral g) σ := rfl

theorem stD_symbol (g : IntegralGL) (L M : Line) :
    stD g (symbol L M) = detQ g • symbol (g • L) (g • M) := by
  rw [stD_apply, action_symbol]
  rfl

theorem smul_cusp1_eq {g : IntegralGL} {x : Line} {v : IntegralVector} (hx : IsGen x v)
    (h : (fun i => g.val i 0) = v ∨ (fun i => g.val i 0) = -v) : g • cusp1 = x := by
  have h0 : IsGen (g • cusp1) (fun i => g.val i 0) := by
    rw [smul_cusp1]; exact col_isGen g 0
  exact ((hx.line_eq_iff h0).mpr (by tauto)).symm

theorem smul_cusp2_eq {g : IntegralGL} {x : Line} {v : IntegralVector} (hx : IsGen x v)
    (h : (fun i => g.val i 1) = v ∨ (fun i => g.val i 1) = -v) : g • cusp2 = x := by
  have h0 : IsGen (g • cusp2) (fun i => g.val i 1) := by
    rw [smul_cusp2]; exact col_isGen g 1
  exact ((hx.line_eq_iff h0).mpr (by tauto)).symm

theorem stab_p0_cusps (g : IntegralGL) (hg : g ∈ MulAction.stabilizer IntegralGL p0) :
    (g • cusp1 = cusp1 ∧ g • cusp2 = cusp2 ∧ detQ g = 1) ∨
    (g • cusp1 = cusp2 ∧ g • cusp2 = cusp1 ∧ detQ g = -1) := by
  rcases stab_p0_entries g hg with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · left
    refine ⟨smul_cusp1_eq isGen_cusp1 (Or.inl ?_), smul_cusp2_eq isGen_cusp2 (Or.inl ?_), ?_⟩
    · funext i; fin_cases i <;> simp [e1, a, c]
    · funext i; fin_cases i <;> simp [e2, b, d]
    · rw [detQ_eq, a, b, c, d]; norm_num
  · left
    refine ⟨smul_cusp1_eq isGen_cusp1 (Or.inr ?_), smul_cusp2_eq isGen_cusp2 (Or.inr ?_), ?_⟩
    · funext i; fin_cases i <;> simp [e1, a, c]
    · funext i; fin_cases i <;> simp [e2, b, d]
    · rw [detQ_eq, a, b, c, d]; norm_num
  · right
    refine ⟨smul_cusp1_eq isGen_cusp2 (Or.inl ?_), smul_cusp2_eq isGen_cusp1 (Or.inl ?_), ?_⟩
    · funext i; fin_cases i <;> simp [e2, a, c]
    · funext i; fin_cases i <;> simp [e1, b, d]
    · rw [detQ_eq, a, b, c, d]; norm_num
  · right
    refine ⟨smul_cusp1_eq isGen_cusp2 (Or.inr ?_), smul_cusp2_eq isGen_cusp1 (Or.inr ?_), ?_⟩
    · funext i; fin_cases i <;> simp [e2, a, c]
    · funext i; fin_cases i <;> simp [e1, b, d]
    · rw [detQ_eq, a, b, c, d]; norm_num

theorem reference_eq : reference = symbol cusp1 cusp2 := by
  rw [reference, ← cusp1_eq, ← cusp2_eq]

theorem stD_stab_reference (g : IntegralGL) (hg : g ∈ MulAction.stabilizer IntegralGL p0) :
    stD g reference = reference := by
  rw [reference_eq, stD_symbol]
  rcases stab_p0_cusps g hg with ⟨h1, h2, hd⟩ | ⟨h1, h2, hd⟩
  · rw [h1, h2, hd, one_smul]
  · rw [h1, h2, hd, symbol_reverse]; simp


/-- The symbol of an oriented dual edge: `det γ • γ • reference` for `q = γ • p0`. -/
def edgeSym (q : OTE) : St := stD (Classical.choose (ote_transitive q)) reference

theorem edgeSym_apply (γ : IntegralGL) : edgeSym (γ • p0) = stD γ reference := by
  set a := Classical.choose (ote_transitive (γ • p0)) with ha
  have h : a • p0 = γ • p0 := Classical.choose_spec (ote_transitive (γ • p0))
  have hs : γ⁻¹ * a ∈ MulAction.stabilizer IntegralGL p0 := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, h, inv_smul_smul]
  have hst := stD_stab_reference _ hs
  unfold edgeSym
  rw [← ha]
  calc stD a reference = stD (γ * (γ⁻¹ * a)) reference := by rw [mul_inv_cancel_left]
    _ = stD γ (stD (γ⁻¹ * a) reference) := by rw [map_mul]; rfl
    _ = stD γ reference := by rw [hst]

theorem edgeSym_smul (g : IntegralGL) (q : OTE) : edgeSym (g • q) = stD g (edgeSym q) := by
  obtain ⟨γ, rfl⟩ := ote_transitive q
  rw [← mul_smul, edgeSym_apply, edgeSym_apply, map_mul]
  rfl

theorem edgeSym_p0 : edgeSym p0 = reference := by
  have := edgeSym_apply 1
  rwa [one_smul, map_one] at this

theorem sOne_cusp1 : sOne • cusp1 = cusp1 :=
  smul_cusp1_eq isGen_cusp1 (Or.inl (by funext i; fin_cases i <;> simp [sOne, colGL_val_zero, e1]))

theorem sOne_cusp2 : sOne • cusp2 = cusp2 :=
  smul_cusp2_eq isGen_cusp2 (Or.inr (by funext i; fin_cases i <;> simp [sOne, colGL_val_one, e2]))

theorem detQ_sOne : detQ sOne = -1 := by
  rw [detQ_eq]; simp [sOne, colGL_val_zero, colGL_val_one, e1, e2]

theorem stD_sOne_reference : stD sOne reference = - reference := by
  rw [reference_eq, stD_symbol, sOne_cusp1, sOne_cusp2, detQ_sOne]
  exact neg_one_smul ℚ (symbol cusp1 cusp2)

theorem edgeSym_swap (q : OTE) : edgeSym q.swap = - edgeSym q := by
  obtain ⟨γ, rfl⟩ := ote_transitive q
  have : (γ • p0).swap = (γ * sOne) • p0 := by
    rw [OTE.swap_smul, mul_smul, sOne_smul_p0]
  rw [this, edgeSym_apply, edgeSym_apply, map_mul]
  change stD γ (stD sOne reference) = _
  rw [stD_sOne_reference, map_neg]

/-- The symbol map `ℚ[OTE] → St^δ`, sending the standard oriented edge to the reference symbol. -/
def piT : Rep.ofMulAction ℚ IntegralGL OTE ⟶ StD :=
  permLift StD edgeSym (fun g x => edgeSym_smul g x)

theorem piT_single (q : OTE) (r : ℚ) :
    piT.hom (MonoidAlgebra.single q r) = r • edgeSym q := permLift_single _ _ _ _ _

theorem piT_surjective : Function.Surjective piT.hom := by
  have hspan : LinearMap.range piT.hom.toLinearMap = ⊤ := by
    rw [eq_top_iff, ← integralSpan_eq_top]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, rfl⟩
    refine ⟨detQ g • MonoidAlgebra.single (g • p0) (1 : ℚ), ?_⟩
    change piT.hom (detQ g • MonoidAlgebra.single (g • p0) (1 : ℚ)) = _
    rw [map_smul, piT_single, edgeSym_apply, one_smul, stD_apply, smul_smul, detQ_mul_self g, one_smul]
  intro σ
  have : σ ∈ LinearMap.range piT.hom.toLinearMap := by rw [hspan]; trivial
  exact this

end TernaryPeriodPolynomials.Argument.HeckeDuality
