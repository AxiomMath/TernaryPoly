module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Inflation
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.PermEval

@[expose] public section


/-!
# The standard-edge coefficient on `(M ⊗ P1)_Q`

Formalized by Claude Sonnet 5.5.

For `π : Q →* GL₂(ℤ)` (the quotient `Q = P_H/U` of `P_H`), `evalQ π hker M : (M ⊗ Res_π P1)_Q → M` reads the coefficient at the
standard oriented edge `p0` of the dual Farey tree: `[m ⊗ y] ↦ ∑_{q : π q • y = p0} q m` extended to antisymmetric chains
(`evalAt` of `BinaryDuality.PermEval` for the `Q`-set of oriented edges).  `evalQ_nat`: it is natural in `Q`-morphisms of `M`.
`evalQ_infl`: for a `GL₂(ℤ)`-representation `W` it equals `|ker π|` times the `GL₂(ℤ)`-evaluation `evalP W` of the inflated class
(`inflEquiv`), because the fibres of the surjection `π` have `|ker π|` elements (`card_fiber`, `normAt_infl`).
-/

open CategoryTheory MonoidalCategory Representation Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.BinaryDuality
  TernaryPoly.RankTwoAugmentedFrames

section

variable {Q : Type} [Group Q] (π : Q →* IntegralGL)

/-- The `Q`-action on the oriented edges through `π`. -/
@[reducible] def oteMulActionQ : MulAction Q OTE := MulAction.compHom OTE π

theorem res_PE_eq : Rep.res π PE = @Rep.ofMulAction ℚ Q _ _ OTE (oteMulActionQ π) := rfl

theorem stab_finite_Q (hker : (π.ker : Set Q).Finite) :
    letI : MulAction Q OTE := oteMulActionQ π
    Finite (MulAction.stabilizer Q p0) := by
  let _ : MulAction Q OTE := oteMulActionQ π
  have h1 : ((MulAction.stabilizer IntegralGL p0 : Set IntegralGL)).Finite := by
    have := ote_stabilizer_finite p0
    exact Set.toFinite _
  have h2 : (π ⁻¹' (MulAction.stabilizer IntegralGL p0 : Set IntegralGL)).Finite :=
    h1.preimage' (fun b _ => preimage_fibre_finite π hker b)
  have h3 : ((MulAction.stabilizer Q p0 : Set Q)).Finite := by
    refine h2.subset ?_
    intro q hq
    change π q • p0 = p0
    exact hq
  exact h3.to_subtype

/-- The coefficient at the standard oriented edge of a class in `(M ⊗ P1)_Q` (`Q` acting through `π`). -/
def evalQ (hker : (π.ker : Set Q).Finite) (M : Rep.{0} ℚ Q) :
    (FX (Rep.res π P1)).obj M →ₗ[ℚ] M :=
  letI : MulAction Q OTE := oteMulActionQ π
  (evalAt (X := OTE) (x₀ := p0) (stab_finite_Q π hker) M) ∘ₗ
    ((FXmap (Rep.resMap π inclP1)).app M).hom

theorem normAt_equiv (hfin : letI : MulAction Q OTE := oteMulActionQ π
    Finite (MulAction.stabilizer Q p0)) {M N : Rep.{0} ℚ Q} (ψ : M ⟶ N) (y : OTE) (m : M) :
    letI : MulAction Q OTE := oteMulActionQ π
    normAt hfin N y (ψ.hom m) = ψ.hom (normAt hfin M y m) := by
  let _ : MulAction Q OTE := oteMulActionQ π
  unfold normAt
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact (Rep.hom_comm_apply ψ q m).symm

theorem evalTen_equiv (hfin : letI : MulAction Q OTE := oteMulActionQ π
    Finite (MulAction.stabilizer Q p0)) {M N : Rep.{0} ℚ Q} (ψ : M ⟶ N) (m : M) (c : MonoidAlgebra ℚ OTE) :
    letI : MulAction Q OTE := oteMulActionQ π
    evalTen hfin N (ψ.hom m ⊗ₜ c) = ψ.hom (evalTen hfin M (m ⊗ₜ c)) := by
  let _ : MulAction Q OTE := oteMulActionQ π
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
  | single y r =>
    rw [evalTen_tmul_single, evalTen_tmul_single, normAt_equiv π hfin ψ, map_smul]

theorem evalQ_nat (hker : (π.ker : Set Q).Finite) {M N : Rep.{0} ℚ Q} (ψ : M ⟶ N)
    (w : (FX (Rep.res π P1)).obj M) :
    evalQ π hker N (((FX (Rep.res π P1)).map ψ).hom w) = ψ.hom (evalQ π hker M w) := by
  let _ : MulAction Q OTE := oteMulActionQ π
  induction w using Coinvariants.induction_on with
  | h v =>
    induction v using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul m p =>
      have h1 : ((FX (Rep.res π P1)).map ψ).hom (Coinvariants.mk _ (m ⊗ₜ[ℚ] p)) =
          Coinvariants.mk _ (ψ.hom m ⊗ₜ[ℚ] p) := FX_map_mk ψ m p
      rw [h1]
      change evalTen _ N (ψ.hom m ⊗ₜ[ℚ] (p : MonoidAlgebra ℚ OTE)) =
        ψ.hom (evalTen _ M (m ⊗ₜ[ℚ] (p : MonoidAlgebra ℚ OTE)))
      exact evalTen_equiv π _ ψ m _

theorem card_fiber (hπ : Function.Surjective π) (γ : IntegralGL) :
    Nat.card (π ⁻¹' {γ}) = Nat.card π.ker := by
  obtain ⟨q0, hq0⟩ := hπ γ
  refine Nat.card_congr
    { toFun := fun q => ⟨q0⁻¹ * q.1, by
        have h : π q.1 = γ := q.2
        change π (q0⁻¹ * q.1) = 1
        rw [map_mul, map_inv, hq0, h]; simp⟩
      invFun := fun k => ⟨q0 * k.1, by
        have h : π k.1 = 1 := k.2
        change π (q0 * k.1) = γ
        rw [map_mul, hq0, h]; simp⟩
      left_inv := fun q => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp) }

theorem normAt_infl (hπ : Function.Surjective π) (hker : (π.ker : Set Q).Finite)
    (W : Rep.{0} ℚ IntegralGL) (y : OTE) (n : W) :
    letI : MulAction Q OTE := oteMulActionQ π
    normAt (stab_finite_Q π hker) (Rep.res π W) y n =
      (Nat.card π.ker : ℚ) • normAt (ote_stabilizer_finite p0) W y n := by
  let _ : MulAction Q OTE := oteMulActionQ π
  unfold normAt
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Finset.smul_sum]
  have hmaps : ∀ q ∈ (transp_finite (stab_finite_Q π hker) y).toFinset,
      π q ∈ (transp_finite (ote_stabilizer_finite p0) y).toFinset := by
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq ⊢
    exact hq
  have h := Finset.sum_fiberwise_of_maps_to' (s := (transp_finite (stab_finite_Q π hker) y).toFinset)
    (t := (transp_finite (ote_stabilizer_finite p0) y).toFinset) hmaps (fun γ => W.ρ γ n)
  refine Eq.trans (h.symm) ?_
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [Finset.sum_const]
  have hcard : (Finset.filter (fun i => π i = γ) (transp_finite (stab_finite_Q π hker) y).toFinset).card =
      Nat.card π.ker := by
    rw [← card_fiber π hπ γ]
    rw [Set.Finite.mem_toFinset] at hγ
    have : (Finset.filter (fun i => π i = γ) (transp_finite (stab_finite_Q π hker) y).toFinset : Set Q) =
        π ⁻¹' {γ} := by
      ext q
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · exact fun h => h.2
      · intro hq
        refine ⟨?_, hq⟩
        change π q • y = p0
        rw [hq]; exact hγ
    rw [← this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hcard, Nat.cast_smul_eq_nsmul]

theorem evalTen_infl (hπ : Function.Surjective π) (hker : (π.ker : Set Q).Finite)
    (W : Rep.{0} ℚ IntegralGL) (n : W) (c : MonoidAlgebra ℚ OTE) :
    letI : MulAction Q OTE := oteMulActionQ π
    evalTen (stab_finite_Q π hker) (Rep.res π W) (n ⊗ₜ c) =
      (Nat.card π.ker : ℚ) • evalTen (ote_stabilizer_finite p0) W (n ⊗ₜ c) := by
  let _ : MulAction Q OTE := oteMulActionQ π
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb, smul_add]
  | single y r =>
    rw [evalTen_tmul_single, evalTen_tmul_single, normAt_infl π hπ hker, smul_comm]

/-- **The `Q`-evaluation at the standard edge is `|ker π|` times the `Γ`-evaluation.** -/
theorem evalQ_infl (hπ : Function.Surjective π) (hker : (π.ker : Set Q).Finite) (W : Rep.{0} ℚ IntegralGL)
    (w : (FX (Rep.res π P1)).obj (Rep.res π W)) :
    evalQ π hker (Rep.res π W) w =
      (Nat.card π.ker : ℚ) • evalP W ((inclC W).hom (inflEquiv π hπ W P1 w)) := by
  let _ : MulAction Q OTE := oteMulActionQ π
  induction w using Coinvariants.induction_on with
  | h v =>
    induction v using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb, smul_add]
    | tmul m p =>
      change evalTen _ (Rep.res π W) (m ⊗ₜ[ℚ] (p : MonoidAlgebra ℚ OTE)) =
        (Nat.card π.ker : ℚ) • evalTen (ote_stabilizer_finite p0) W (m ⊗ₜ[ℚ] (p : MonoidAlgebra ℚ OTE))
      exact evalTen_infl π hπ hker W m _

end

end TernaryPeriodPolynomials.Argument.HochschildSerre
