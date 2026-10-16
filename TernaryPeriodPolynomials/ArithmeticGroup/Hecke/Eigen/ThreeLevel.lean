module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Stability.AwayThreeStability
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaneLevelFactorization
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.AwayHecke

@[expose] public section


/-!
# Representatives of away-from-three correspondences at the place three

For an `AwayThree` correspondence every representative lies, at the place three, in the local
level `K₁(3)`. Every integral finite matrix splits as a factor supported at three times an element
of `finiteLevel`, and that factor commutes with every finite matrix trivial at three. Right
`finiteLevel`-invariant functions (with values in any additive monoid) have Hecke sums that are
again right `finiteLevel`-invariant.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.HeckeEigen

theorem integralAtThree_norm {x : ℚ} (hx : IntegralAtThree x) : ‖(x : ℚ_[3])‖ ≤ 1 := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  have hb' : ¬ ((3 : ℕ) : ℤ) ∣ b := by
    intro h; apply hb; exact (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mpr h
  have hcast : ‖((b : ℤ_[3]) : ℚ_[3])‖ = ‖(b : ℚ_[3])‖ := by push_cast; rfl
  have hbn : ‖(b : ℚ_[3])‖ = 1 := by
    refine le_antisymm (Padic.norm_int_le_one b) (not_lt.mp (fun h => hb' ?_))
    apply (PadicInt.norm_int_lt_one_iff_dvd b).mp
    rw [PadicInt.norm_def, hcast]
    exact h
  push_cast
  rw [norm_div, hbn, div_one]
  exact Padic.norm_int_le_one a

/-- The integral `3`-adic matrix with prescribed rational entries. -/
def threeIntegralMatrix (M : Matrix (Fin 3) (Fin 3) ℚ) (hM : ∀ i j, IntegralAtThree (M i j)) :
    Matrix (Fin 3) (Fin 3) ℤ_[3] :=
  fun i j => ⟨(M i j : ℚ_[3]), integralAtThree_norm (hM i j)⟩

theorem threeIntegralMatrix_map (M : Matrix (Fin 3) (Fin 3) ℚ) (hM : ∀ i j, IntegralAtThree (M i j)) :
    (threeIntegralMatrix M hM).map PadicInt.Coe.ringHom = M.map (algebraMap ℚ ℚ_[3]) := by
  ext i j; rfl

theorem padicCoe_injective : Function.Injective (PadicInt.Coe.ringHom : ℤ_[3] →+* ℚ_[3]) :=
  Subtype.coe_injective

/-- The defining matrix of an `AwayThree` correspondence lies in the local level at three. -/
theorem awayThree_local_level {t : HeckeCorrespondence} (ht : AwayThree t) :
    InLocalThreeLevel (GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) t.g) := by
  set K := threeIntegralMatrix t.g.val (fun i j => (ht.1 i j).1)
  set Ki := threeIntegralMatrix (t.g⁻¹).val (fun i j => (ht.1 i j).2)
  have hmul : K * Ki = 1 := by
    apply Matrix.map_injective padicCoe_injective
    beta_reduce
    rw [Matrix.map_mul, threeIntegralMatrix_map, threeIntegralMatrix_map, ← Matrix.map_mul,
      Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
  let k : GeneralLinearGroup (Fin 3) ℤ_[3] := ⟨K, Ki, hmul, mul_eq_one_comm.mp hmul⟩
  refine ⟨k, ?_, ?_⟩
  · change lastRow ᵥ* (K.map PadicInt.toZMod) = lastRow
    funext j
    have hrow := ht.2 j
    set y : ℤ_[3] := ⟨(((t.g.val 2 j - if j = 2 then 1 else 0) / 3 : ℚ) : ℚ_[3]),
      integralAtThree_norm hrow⟩
    have key : K 2 j = (if j = 2 then 1 else 0 : ℤ_[3]) + 3 * y := by
      apply Subtype.ext
      change ((t.g.val 2 j : ℚ) : ℚ_[3]) = ((if j = 2 then 1 else 0 : ℤ_[3]) : ℚ_[3]) +
        3 * ((((t.g.val 2 j - if j = 2 then 1 else 0) / 3 : ℚ) : ℚ_[3]))
      split_ifs <;> push_cast <;> ring
    have h3 : PadicInt.toZMod (3 : ℤ_[3]) = 0 := by
      rw [map_ofNat]; decide
    simp only [vecMul, dotProduct, Fin.sum_univ_three, lastRow, Matrix.map_apply]
    simp only [Pi.single_apply, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
      ite_false, ite_true, zero_mul, one_mul, zero_add]
    rw [key, map_add, map_mul, h3, zero_mul, add_zero]
    split_ifs with h
    · simp
    · simp
  · apply Units.ext
    exact threeIntegralMatrix_map t.g.val (fun i j => (ht.1 i j).1)

theorem rationalFinite_three (x : RationalGL3) :
    GeneralLinearGroup.map finiteThree (rationalFinite x) =
      GeneralLinearGroup.map (algebraMap ℚ ℚ_[3]) x := by
  exact adelicThreeGroup_rational x

/-- Every representative of an `AwayThree` correspondence lies, at three, in the local level. -/
theorem rep_local_level {t : HeckeCorrespondence} (ht : AwayThree t) {r : RationalGL3}
    (hr : r ∈ t.representatives) :
    InLocalThreeLevel (GeneralLinearGroup.map finiteThree (rationalFinite r)) := by
  obtain ⟨a, b, rfl⟩ := t.inDoubleCoset r hr
  rw [rationalFinite_three, map_mul, map_mul]
  obtain ⟨a₀, ha₀⟩ := a.property
  obtain ⟨b₀, hb₀⟩ := b.property
  rw [← ha₀, ← hb₀]
  exact InLocalThreeLevel_mul (InLocalThreeLevel_mul (arithmeticLevel_atThree a₀)
    (awayThree_local_level ht)) (arithmeticLevel_atThree b₀)

/-- Hecke sums of right `finiteLevel`-invariant functions are right `finiteLevel`-invariant. -/
theorem heckeSum_level {M : Type*} [AddCommMonoid M] (t : HeckeCorrespondence)
    (F : AdelicGL → M) (hF : ∀ g (k : finiteLevel), F (g * atFinite k.val) = F g)
    (g : AdelicGL) {k : FiniteGL} (hk : k ∈ finiteLevel) :
    ∑ r ∈ t.representatives, F (g * atFinite (k * rationalFinite r)) =
      ∑ r ∈ t.representatives, F (g * atFinite (rationalFinite r)) := by
  classical
  have hperm := HeckeStability.cosetPermutation_all t
  rw [← Finset.sum_coe_sort t.representatives]
  conv_rhs => rw [← Finset.sum_coe_sort t.representatives]
  have hchoice : ∀ r : t.representatives, ∃ r' : t.representatives,
      (rationalFinite r'.val)⁻¹ * k * rationalFinite r.val ∈ finiteLevel := by
    intro r
    obtain ⟨r', hr', hmem⟩ := hperm k hk r.val r.property
    exact ⟨⟨r', hr'⟩, hmem⟩
  choose σ hσ using hchoice
  have hinj : Function.Injective σ := by
    intro r₁ r₂ heq
    have h₁ := hσ r₁
    have h₂ := hσ r₂
    rw [heq] at h₁
    have hprod := finiteLevel.mul_mem (finiteLevel.inv_mem h₁) h₂
    have hsimp : ((rationalFinite (σ r₂).val)⁻¹ * k * rationalFinite r₁.val)⁻¹ *
        ((rationalFinite (σ r₂).val)⁻¹ * k * rationalFinite r₂.val) =
        rationalFinite (r₁.val⁻¹ * r₂.val) := by
      rw [map_mul, map_inv]; group
    rw [hsimp] at hprod
    have hlevel := (HeckeStability.rationalFinite_mem_finiteLevel_iff _).mp hprod
    exact Subtype.ext (t.disjoint r₁.val r₁.property r₂.val r₂.property hlevel)
  have hbij : Function.Bijective σ := ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hterm : ∀ r : t.representatives,
      F (g * atFinite (k * rationalFinite r.val)) = F (g * atFinite (rationalFinite (σ r).val)) := by
    intro r
    have hm : k * rationalFinite r.val = rationalFinite (σ r).val *
        ((rationalFinite (σ r).val)⁻¹ * k * rationalFinite r.val) := by group
    rw [hm, ← HeckeTranslate.HeckeInvariance.atFinite_mul, ← mul_assoc]
    exact hF _ ⟨_, hσ r⟩
  rw [Finset.sum_congr rfl (fun r _ => hterm r)]
  exact Fintype.sum_bijective σ hbij _ _ (fun _ => rfl)

/-- Finite matrices supported at three commute with finite matrices trivial at three. -/
theorem threePart_commute (a : GeneralLinearGroup (Fin 3) (placeThree.adicCompletion ℚ))
    {y : FiniteGL} (hy : GeneralLinearGroup.map (finiteEvaluation placeThree) y = 1) :
    finiteAtPlaceGL 3 placeThree a * y = y * finiteAtPlaceGL 3 placeThree a := by
  apply finiteGeneralLinearGroup_ext
  intro w
  rw [map_mul, map_mul]
  by_cases h : w = placeThree
  · subst h; rw [hy, one_mul, mul_one]
  · rw [finiteAtPlaceGL_away 3 placeThree a w h, one_mul, mul_one]

theorem finiteThree_eq_one_iff (x : FiniteGL) :
    GeneralLinearGroup.map finiteThree x = 1 ↔
      GeneralLinearGroup.map (finiteEvaluation placeThree) x = 1 := by
  have hcomp : GeneralLinearGroup.map finiteThree x = GeneralLinearGroup.map
      threeCompletionEquiv.toAlgEquiv.toRingEquiv.toRingHom
      (GeneralLinearGroup.map (finiteEvaluation placeThree) x) := by
    apply Units.ext; rfl
  rw [hcomp]
  constructor
  · intro h
    apply generalLinearGroup_map_injective threeCompletionEquiv.toAlgEquiv.toRingEquiv.toRingHom
      threeCompletionEquiv.injective
    rw [h, map_one]
  · intro h; rw [h, map_one]

/-- Every integral finite matrix is a factor supported at three times an element of
`finiteLevel`. -/
theorem integral_split_three (κ : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    ∃ κ₃ : GeneralLinearGroup (Fin 3) (placeThree.adicCompletion ℚ), ∃ κ' : finiteLevel,
      GeneralLinearGroup.map integralEmbedding κ = finiteAtPlaceGL 3 placeThree κ₃ * κ'.val := by
  set K := GeneralLinearGroup.map integralEmbedding κ
  set κ₃ := GeneralLinearGroup.map (finiteEvaluation placeThree) K
  have hint : finiteAtPlaceGL 3 placeThree κ₃ ∈ finiteIntegralGLLevel 3 := by
    have : κ₃ = GeneralLinearGroup.map (placeThree.adicCompletionIntegers ℚ).toSubring.subtype
        (GeneralLinearGroup.map (Pi.evalRingHom _ placeThree) κ) := by
      apply Units.ext; funext i j; rfl
    rw [this]
    exact finiteAtPlaceGL_integral 3 placeThree _
  have hlev : (finiteAtPlaceGL 3 placeThree κ₃)⁻¹ * K ∈ finiteLevel := by
    apply finiteLevel_of_integral_of_three
    · exact (finiteIntegralGLLevel 3).mul_mem ((finiteIntegralGLLevel 3).inv_mem hint) ⟨κ, rfl⟩
    · rw [(finiteThree_eq_one_iff _).mpr (by rw [map_mul, map_inv, finiteAtPlaceGL_same, inv_mul_cancel])]
      exact ⟨1, by simp, by simp⟩
  exact ⟨κ₃, ⟨_, hlev⟩, by simp⟩

end TernaryPeriodPolynomials.HeckeEigen
