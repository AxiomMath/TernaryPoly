module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.ShapiroUnit
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.CosetSumAbs
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Literal.DualityNatural

@[expose] public section


/-!
# `shapiroG` versus Mathlib's Shapiro isomorphism: the comparison and its exact scalar

Formalized by Claude Sonnet 5.5.

`LevelG/MathlibShapiro.lean` states
`ShapiroComparison n t` (the duality-defined `shapiroG` equals Mathlib's `groupHomology.indIso`, with scalar `1`) as open.

* `Naturality/ShapiroUnit.lean`: `mathlibShapiro_inv`: the inverse of Mathlib's isomorphism is `Cor_K^G ∘ ι_*`
  (`groupHomology.map K.subtype ι 3`), `ι` the identity-coset inclusion (`iotaK_apply`).
* Here: `frobenius_thetaG_cor`: `frobenius (Θ^G (Cor_K^G ι_* w)) = [G:K]⁻¹ • Θ^K w`.  The proof is the Mackey bookkeeping for the
  non-normal `K`: reduce to `Γ(6)` (`pushN`, `psiGen_pushN`, `cor_pushN`), average over `G/Γ(6)`, only the cosets inside `K` survive
  (`eval_term`, `sum_quot_eq`), and `|G/Γ(6)| = [G:K] |K/Γ(6)|` (`card_quot_mul`).
* Consequences: `mathlibShapiro_eq_index_smul` (`mathlibShapiro = [G:K] • shapiroG`), `shapiroComparison_scaled` (the corrected
  comparison, true), and `shapiroComparison_iff_trivial`: `ShapiroComparison` with scalar `1` holds iff `H₃(G, M_{n,t}) = 0`.
-/

open CategoryTheory TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction
  TernaryPoly.OrdinaryBoundaryCommonRoot TernaryPoly.OrdinaryBoundaryActualEvaluation
open TernaryPoly.PolynomialGLAction TernaryPoly.OrdinaryCovectors
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.LevelG
open TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPeriodPolynomials.Argument.Lemma45Literal

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open scoped Classical
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- On the image of corestriction the `K`-level duality is the averaged neat-level duality. -/
theorem H3_K_equiv_corN (n : ℕ) (t : Fin 2)
    (z : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3) :
    ((H3_K_equiv n t (corN principalSixInK (EK n t) 3 z)).val) =
      psi n t (avgN principalSixInK (EK n t) 3 z) := by
  unfold TernaryPeriodPolynomials.Argument.Statements.FiberModel.H3_K_equiv TernaryPeriodPolynomials.Argument.Statements.FiberModel.H3_K_equiv_of_neat_equivariance kEquivOfEquivariance
  simp only [LinearEquiv.trans_apply]
  have h1 : ∀ (e : (LinearMap.range (avgN principalSixInK (EK n t) 3)) ≃ₗ[ℚ] groupHomology (EK n t) 3)
      (he : ∀ w, e w = corN principalSixInK (EK n t) 3 w.1),
      e.symm (corN principalSixInK (EK n t) 3 z) = ⟨avgN principalSixInK (EK n t) 3 z, z, rfl⟩ := by
    intro e he
    rw [LinearEquiv.symm_apply_eq, he]
    exact (corN_avgN z).symm
  rw [h1 _ (fun _ => rfl)]
  rfl

/-- `ι` restricted to `Γ(6)`, as a morphism of `Γ(6)`-representations. -/
def iotaN (n : ℕ) (t : Fin 2) : EGamma n t ⟶ Rep.res principalSix.subtype (MG n t) :=
  Rep.ofHom ⟨(iotaK n t).hom.toLinearMap, fun γ => LinearMap.ext fun a =>
    Rep.hom_comm_apply (iotaK n t) ⟨γ.1, principalSix_le_K γ.2⟩ a⟩

/-- The copy of `Γ(6)` inside `K` identified with `Γ(6)`, on `H₃(-, E_{n,t})`. -/
def mapSix (n : ℕ) (t : Fin 2) :
    groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3 ≅ groupHomology (EGamma n t) 3 :=
  groupHomology.mapIso sixEquiv (LinearEquiv.refl ℚ (V n)) (fun _ => rfl) 3

/-- The neat-level class `y` of `H₃(Γ(6)-in-K, E)`, pushed to `H₃(Γ(6), Res M)` along `ι`. -/
def pushN (n : ℕ) (t : Fin 2) :
    groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3 →ₗ[ℚ]
      groupHomology (Rep.res principalSix.subtype (MG n t)) 3 :=
  (groupHomology.map (MonoidHom.id principalSix) (iotaN n t) 3).hom ∘ₗ (mapSix n t).hom.hom

theorem psiGen_pushN (n : ℕ) (t : Fin 2) (y : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3) :
    psiGen principalSix (MulEquiv.refl ↥principalSix) (MG n t) (pushN n t y) =
      (iotaK n t).hom.toLinearMap ∘ₗ psi n t y := by
  have e1 := thetaGen_refl_apply (MG n t) (pushN n t y)
  have e3 := TernaryPeriodPolynomials.Argument.CoefficientNaturality.groupOrdinaryIso_natural (iotaN n t)
    ((mapSix n t).hom.hom y)
  apply LinearMap.ext
  intro c
  change (((thetaGen principalSix (MulEquiv.refl ↥principalSix) (MG n t)).hom.hom (pushN n t y)).hom c) = _
  rw [e1]
  have e4 : pushN n t y = (groupHomology.map (MonoidHom.id principalSix) (iotaN n t) 3).hom ((mapSix n t).hom.hom y) := rfl
  rw [e4, e3]
  rfl

theorem cor_pushN (n : ℕ) (t : Fin 2) (y : groupHomology (Rep.res principalSixInK.subtype (EK n t)) 3) :
    corN principalSix (MG n t) 3 (pushN n t y) =
      (groupHomology.map K.subtype (iotaK n t) 3).hom (corN principalSixInK (EK n t) 3 y) := by
  have h : (mapSix n t).hom ≫ groupHomology.map (MonoidHom.id principalSix) (iotaN n t) 3 ≫
        groupHomology.map principalSix.subtype (𝟙 (Rep.res principalSix.subtype (MG n t))) 3 =
      groupHomology.map principalSixInK.subtype (𝟙 (Rep.res principalSixInK.subtype (EK n t))) 3 ≫
        groupHomology.map K.subtype (iotaK n t) 3 := by
    unfold mapSix
    erw [← groupHomology.map_comp, ← groupHomology.map_comp, ← groupHomology.map_comp]
    refine groupHomology.map_congr ?_ ?_ 3
    · ext y
      rfl
    · ext y
      rfl
  exact congrArg (fun f => f.hom y) h

theorem evaluation_iotaK (n : ℕ) (t : Fin 2) (g : IntegralGL) (a : V n) :
    evaluation n (coefficientAction n (expT t) g (Pi.single distinguished a)) =
      if g ∈ K then integralAction n (expT t) g a else 0 := by
  change integralAction n (expT t) g ((Pi.single distinguished a : Coefficients n) (rowMove g distinguished)) = _
  by_cases hg : g ∈ K
  · rw [ite_eq_left hg, (mem_K_iff_rowMove g).mp hg, Pi.single_eq_same]
  · rw [ite_eq_right hg]
    have : rowMove g distinguished ≠ distinguished := fun h => hg ((mem_K_iff_rowMove g).mpr h)
    rw [Pi.single_eq_of_ne this, map_zero]

/-- The summand of the `G`-level average, evaluated at the distinguished covector. -/
theorem eval_term (n : ℕ) (t : Fin 2) (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] V n) (g : IntegralGL)
    (z : OrdinaryIncidenceChains.Cycles) :
    evaluation n (GroupHomology.term stG (MG n t).ρ ((iotaK n t).hom.toLinearMap ∘ₗ Φ) g z) =
      if h : g ∈ K then GroupHomology.term stK (coeffK n t) Φ ⟨g, h⟩ z else 0 := by
  unfold TernaryPeriodPolynomials.Argument.GroupHomology.term
  change evaluation n (coefficientAction n (expT t) g ((iotaK n t).hom (Φ (stG g⁻¹ z)))) = _
  rw [iotaK_apply, evaluation_iotaK]
  by_cases h : g ∈ K
  · rw [dite_eq_left h, ite_eq_left h]
    have h2 : stG g⁻¹ z = stK ⟨g, h⟩⁻¹ z := by
      have := OrdinaryFullAction.cycleAction_K (⟨g, h⟩⁻¹ : K) z
      exact this
    rw [h2]
    rfl
  · rw [dite_eq_right h, ite_eq_right h]

theorem eval_avg (n : ℕ) (t : Fin 2) (Φ : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] V n)
    (hΦ : IsEquivOn stK (coeffK n t) principalSixInK Φ) (z : OrdinaryIncidenceChains.Cycles) :
    evaluation n (avg stG (MG n t).ρ principalSix ((iotaK n t).hom.toLinearMap ∘ₗ Φ) z) =
      ((Nat.card (IntegralGL ⧸ K) : ℚ))⁻¹ • avg stK (coeffK n t) principalSixInK Φ z := by
  have hsum : ∑ q : IntegralGL ⧸ principalSix,
      evaluation n (GroupHomology.term stG (MG n t).ρ ((iotaK n t).hom.toLinearMap ∘ₗ Φ) q.out z) =
      ∑ q' : KT ⧸ principalSixInK, GroupHomology.term stK (coeffK n t) Φ q'.out z := by
    have := sum_quot_eq K principalSix principalSixInK (fun k => mem_principalSixInK k)
      (F := fun g => evaluation n (GroupHomology.term stG (MG n t).ρ ((iotaK n t).hom.toLinearMap ∘ₗ Φ) g z))
      (fun g m hm => by
        have e1 := eval_term n t Φ (g * m) z
        have e2 := eval_term n t Φ g z
        refine e1.trans (Eq.trans ?_ e2.symm)
        by_cases hg : g ∈ K
        · have hgm : g * m ∈ K := K.mul_mem hg (principalSix_le_K hm)
          rw [dite_eq_left hg, dite_eq_left hgm]
          exact GroupHomology.term_mul_right hΦ (g := ⟨g, hg⟩) (n := ⟨m, principalSix_le_K hm⟩)
            ((mem_principalSixInK _).mpr hm) z
        · have hgm : g * m ∉ K := fun h => hg (by simpa using K.mul_mem h (K.inv_mem (principalSix_le_K hm)))
          rw [dite_eq_right hg, dite_eq_right hgm])
      (fun g hg => (eval_term n t Φ g z).trans (dite_eq_right hg))
    refine this.trans (Finset.sum_congr rfl fun q' _ => ?_)
    exact (eval_term n t Φ _ z).trans (dite_eq_left (q'.out : KT).2)
  have hcard := card_quot_mul K principalSix principalSixInK (fun k => mem_principalSixInK k)
    principalSix_le_K
  have hcardQ : ((Fintype.card (IntegralGL ⧸ principalSix) : ℚ))⁻¹ =
      ((Nat.card (IntegralGL ⧸ K) : ℚ))⁻¹ * ((Fintype.card (KT ⧸ principalSixInK) : ℚ))⁻¹ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]
    push_cast
    rw [mul_inv]
  change evaluation n (((Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹) •
    avgSum stG (MG n t).ρ principalSix ((iotaK n t).hom.toLinearMap ∘ₗ Φ) z) = _
  change _ = ((Nat.card (IntegralGL ⧸ K) : ℚ))⁻¹ •
    (((Fintype.card (KT ⧸ principalSixInK) : ℚ)⁻¹) • avgSum stK (coeffK n t) principalSixInK Φ z)
  rw [map_smul, smul_smul, hcardQ]
  congr 1
  unfold avgSum
  rw [map_sum]
  exact hsum

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- **The duality-defined Shapiro isomorphism versus corestriction.**  For `w ∈ H₃(K, E_{n,t})`, the Frobenius image of the
`G`-level duality of `Cor_K^G ι_* w` is `[G:K]⁻¹` times the `K`-level duality of `w`. -/
theorem frobenius_thetaG_cor (n : ℕ) (t : Fin 2) (w : groupHomology (EK n t) 3) :
    frobenius n t (thetaG (MG n t) ((groupHomology.map K.subtype (iotaK n t) 3).hom w)) =
      ((Nat.card (IntegralGL ⧸ K) : ℚ))⁻¹ • H3_K_equiv n t w := by
  obtain ⟨y, rfl⟩ := corN_surjective (A := EK n t) (n := 3) card_ne_zero w
  rw [← cor_pushN]
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  have hK := neatDualityEquivariant_of_capEps n t
    (fun k => TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k (Rep.of (coeff n t)))
  have hG := neatDualityEquivariantGen_of_capEps (MG n t)
    (fun k => TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k (MG n t))
  have e1 := thetaG_corN (MG n t) (pushN n t y)
  have e2 := H3_K_equiv_corN n t y
  have hΦ : IsEquivOn stK (coeffK n t) principalSixInK (psi n t y) :=
    (mem_range_psi_iff n t _).mp ⟨y, rfl⟩
  change evaluation n ((thetaG (MG n t) (corN principalSix (MG n t) 3 (pushN n t y)) :
      OrdinaryIncidenceChains.Cycles →ₗ[ℚ] MG n t) z) = _
  rw [e1, psiGen_avgN hG, psiGen_pushN]
  rw [eval_avg n t _ hΦ z]
  change _ = ((Nat.card (IntegralGL ⧸ K) : ℚ))⁻¹ •
    (((H3_K_equiv n t (corN principalSixInK (EK n t) 3 y)).val : _) z)
  rw [e2, psi_avgN hK]

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
theorem index_K_ne_zero : (Nat.card (IntegralGL ⧸ K) : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero

/-- `K` is a proper subgroup: the index `[G:K]` is not `1`. -/
theorem K_ne_top : K ≠ ⊤ := by
  intro h
  obtain ⟨g, hg⟩ := row_surjective ⟨![1, 0, 0], by
    intro h0; have := congrFun h0 0; simp at this⟩
  have hK : g ∈ K := h ▸ Subgroup.mem_top g
  have h1 : row g = fixedRow := hK
  have h2 : (![1, 0, 0] : Covector) = fixedRow := hg.symm.trans h1
  have := congrFun h2 1
  simp [fixedRow] at this

theorem index_K_ne_one : (Nat.card (IntegralGL ⧸ K)) ≠ 1 := by
  intro h
  exact K_ne_top (Subgroup.index_eq_one.mp h)

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- `shapiroG` composed with the corestriction-of-the-unit Shapiro inverse is `[G:K]⁻¹`. -/
theorem shapiroG_cor (n : ℕ) (t : Fin 2) (u : groupHomology (EK n t) 3) :
    shapiroG n t ((groupHomology.map K.subtype (iotaK n t) 3).hom u) =
      ((Nat.card (IntegralGL ⧸ K) : ℚ))⁻¹ • u := by
  unfold shapiroG
  simp only [LinearEquiv.trans_apply]
  rw [frobenius_thetaG_cor, map_smul]
  simp

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- **Mathlib's Shapiro isomorphism is `[G:K]` times the duality-defined `shapiroG`.** -/
theorem mathlibShapiro_eq_index_smul (n : ℕ) (t : Fin 2) (z : groupHomology (MG n t) 3) :
    (mathlibShapiro n t).hom z = ((Nat.card (IntegralGL ⧸ K) : ℚ)) • shapiroG n t z := by
  have h1 : z = (groupHomology.map K.subtype (iotaK n t) 3).hom ((mathlibShapiro n t).hom z) := by
    rw [← mathlibShapiro_inv]
    exact (congrArg (fun f => f.hom z) (mathlibShapiro n t).hom_inv_id).symm
  conv_rhs => rw [h1, shapiroG_cor, smul_smul, mul_inv_cancel₀ index_K_ne_zero, one_smul]

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- **The corrected comparison obligation**: Mathlib's Shapiro isomorphism, followed by the `K`-level duality `Θ^K`, is
`[G:K]` times the Frobenius image of the `G`-level duality `Θ^G`. -/
theorem shapiroComparison_scaled (n : ℕ) (t : Fin 2) (z : groupHomology (MG n t) 3) :
    H3_K_equiv n t ((mathlibShapiro n t).hom z) =
      ((Nat.card (IntegralGL ⧸ K) : ℚ)) • frobenius n t (thetaG (MG n t) z) := by
  have h := mathlibShapiro_eq_index_smul n t z
  rw [h, map_smul]
  unfold shapiroG
  simp

open TernaryPeriodPolynomials.Argument.Statements.FiberModel (H3_K_equiv) in
/-- **The comparison `ShapiroComparison` of `MathlibShapiro.lean`, as literally stated (scalar `1`), holds exactly when
`H₃(G, M_{n,t}) = 0`**: the two isomorphisms differ by the factor `[G:K]`, the index of the stabilizer of the distinguished
covector (the corestriction `Cor_K^G` is the unnormalised map on coinvariants while `Θ^G`, `Θ^K` are normalised by the
averaging over `G/Γ(6)` and `K/Γ(6)`). -/
theorem shapiroComparison_iff_trivial (n : ℕ) (t : Fin 2) :
    ShapiroComparison n t ↔ ∀ z : groupHomology (MG n t) 3, z = 0 := by
  rw [shapiroG_eq_mathlib_iff]
  constructor
  · intro h z
    have h1 := h z
    rw [mathlibShapiro_eq_index_smul] at h1
    have h2 : (((Nat.card (IntegralGL ⧸ K) : ℚ)) - 1) • shapiroG n t z = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    have hne : ((Nat.card (IntegralGL ⧸ K) : ℚ)) - 1 ≠ 0 := by
      have hpos : 0 < Nat.card (IntegralGL ⧸ K) := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
      have : 2 ≤ Nat.card (IntegralGL ⧸ K) := by
        have := index_K_ne_one; omega
      intro h3
      have : ((Nat.card (IntegralGL ⧸ K) : ℚ)) = 1 := by linarith
      exact index_K_ne_one (by exact_mod_cast this)
    have h4 : shapiroG n t z = 0 := by
      rcases smul_eq_zero.mp h2 with h5 | h5
      · exact absurd h5 hne
      · exact h5
    exact (shapiroG n t).injective (h4.trans (map_zero _).symm)
  · intro h z
    rw [h z]
    simp

end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
