module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Residue

@[expose] public section


/-!
# The residue fibre as `(V_{n+1}/L·V_n) ⊗ (ℚL)^*`

For a rational hyperplane `H = {L = 0}` with chosen equation `L = denominator H`:

* `ResidueFiber n H = V_{n+1} / numeratorRelations n H` is the quotient `V_{n+1}/L·V_n`
  (`fibreEquiv`).
* `lineDual L hL` is the functional `L^∨` on the line `ℚL` with `L^∨(L) = 1`.
  The map `m ↦ m ⊗ L^∨` is an isomorphism
  `V_{n+1}/L·V_n ≅ (V_{n+1}/L·V_n) ⊗ (ℚL)^*` (`residueTensorEquiv`).
  Composing gives `residueFiberTensorEquiv`.
* `residue_fraction_tensor`: the library residue at `H` of the fraction `q/L`
  (presented as `(0, single H q)`) is sent to `[q] ⊗ L^∨`.
* `residue_scale_tensor`: replacing `(p, L)` by `(c·p, c·L)`, `c ≠ 0`, gives the same
  element `[p] ⊗ L^∨`, so the tensor depends only on the rational function `p/L`.
-/

open MvPolynomial
open TernaryPoly.SinglePole
open scoped TensorProduct

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.ResidueTensor

/-- Multiplication by a linear form `L` from degree `n` to degree `n+1`. -/
def mulLin (n : ℕ) (L : V 1) : V n →ₗ[ℚ] V (n+1) where
  toFun p := ⟨L.val * p.val, by
    change (L.val * p.val).IsHomogeneous (n+1)
    have h : (L.val * p.val).IsHomogeneous (1 + n) := IsHomogeneous.mul L.property p.property
    simpa only [Nat.add_comm 1 n] using h⟩
  map_add' p q := Subtype.ext (mul_add _ _ _)
  map_smul' r p := Subtype.ext (mul_smul_comm _ _ _)

/-- The chosen equation of a rational hyperplane, as an element of `V_1`. -/
def equation (H : Normal) : V 1 := ⟨denominator H, denominator_homogeneous H⟩

theorem equation_ne_zero (H : Normal) : equation H ≠ 0 := fun h =>
  denominator_ne_zero H (congrArg Subtype.val h)

/-- The numerator relations of the library fibre are `L·V_n` for the equation `L`. -/
theorem numeratorRelations_eq (n : ℕ) (H : Normal) :
    numeratorRelations n H = LinearMap.range (mulLin n (equation H)) := rfl

/-- The quotient `V_{n+1}/L·V_n`. -/
abbrev quotLin (n : ℕ) (L : V 1) : Type := V (n+1) ⧸ LinearMap.range (mulLin n L)

/-- The residue fibre is the quotient `V_{n+1}/L·V_n`, for the chosen equation `L`. -/
def fibreEquiv (n : ℕ) (H : Normal) : ResidueFiber n H ≃ₗ[ℚ] quotLin n (equation H) :=
  Submodule.quotEquivOfEq _ _ (numeratorRelations_eq n H)

/-- The functional `L^∨` on the line `ℚL`, with `L^∨(L) = 1`. -/
def lineDual (L : V 1) (hL : L ≠ 0) : Module.Dual ℚ (Submodule.span ℚ {L}) :=
  (LinearEquiv.toSpanNonzeroSingleton ℚ (V 1) L hL).symm.toLinearMap

theorem lineDual_self (L : V 1) (hL : L ≠ 0) :
    lineDual L hL ⟨L, Submodule.mem_span_singleton_self L⟩ = 1 := by
  change (LinearEquiv.toSpanNonzeroSingleton ℚ (V 1) L hL).symm ⟨L, _⟩ = 1
  rw [LinearEquiv.symm_apply_eq]
  exact Subtype.ext (one_smul ℚ L).symm

/-- Every functional on the line `ℚL` is a multiple of `L^∨`, by its value at `L`. -/
theorem dual_eq_smul (L : V 1) (hL : L ≠ 0) (g : Module.Dual ℚ (Submodule.span ℚ {L})) :
    g = g ⟨L, Submodule.mem_span_singleton_self L⟩ • lineDual L hL := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.2
  have hx : x = a • (⟨L, Submodule.mem_span_singleton_self L⟩ : Submodule.span ℚ {L}) :=
    Subtype.ext (by rw [← ha]; rfl)
  rw [hx]
  simp only [map_smul, LinearMap.smul_apply, lineDual_self, smul_eq_mul]
  ring

/-- The map `[p] ↦ [p] ⊗ L^∨`. -/
def toTensor (n : ℕ) (L : V 1) (hL : L ≠ 0) :
    quotLin n L →ₗ[ℚ] quotLin n L ⊗[ℚ] Module.Dual ℚ (Submodule.span ℚ {L}) :=
  (TensorProduct.mk ℚ (quotLin n L) (Module.Dual ℚ (Submodule.span ℚ {L}))).flip (lineDual L hL)

theorem toTensor_apply (n : ℕ) (L : V 1) (hL : L ≠ 0) (m : quotLin n L) :
    toTensor n L hL m = m ⊗ₜ[ℚ] lineDual L hL := rfl

/-- The map `m ⊗ g ↦ g(L) • m`. -/
def fromTensor (n : ℕ) (L : V 1) :
    quotLin n L ⊗[ℚ] Module.Dual ℚ (Submodule.span ℚ {L}) →ₗ[ℚ] quotLin n L :=
  TensorProduct.lift (LinearMap.mk₂ ℚ
    (fun (m : quotLin n L) (g : Module.Dual ℚ (Submodule.span ℚ {L})) =>
      g ⟨L, Submodule.mem_span_singleton_self L⟩ • m)
    (fun m₁ m₂ g => by simp [smul_add])
    (fun c m g => by simp [smul_comm c])
    (fun m g₁ g₂ => by simp [add_smul])
    (fun c m g => by simp [mul_smul]))

theorem fromTensor_tmul (n : ℕ) (L : V 1) (m : quotLin n L)
    (g : Module.Dual ℚ (Submodule.span ℚ {L})) :
    fromTensor n L (m ⊗ₜ[ℚ] g) = g ⟨L, Submodule.mem_span_singleton_self L⟩ • m := by
  simp [fromTensor]

/-- The explicit isomorphism `V_{n+1}/L·V_n ≅ (V_{n+1}/L·V_n) ⊗ (ℚL)^*`. -/
def residueTensorEquiv (n : ℕ) (L : V 1) (hL : L ≠ 0) :
    quotLin n L ≃ₗ[ℚ] quotLin n L ⊗[ℚ] Module.Dual ℚ (Submodule.span ℚ {L}) :=
  LinearEquiv.ofLinearMap (toTensor n L hL) (fromTensor n L)
    (by
      apply TensorProduct.ext'
      intro x g
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [fromTensor_tmul, toTensor_apply]
      conv_rhs => rw [dual_eq_smul L hL g]
      simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul])
    (by
      apply LinearMap.ext
      intro m
      obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      simp [toTensor_apply, fromTensor_tmul, lineDual_self])

/-- The residue fibre is isomorphic to `(V_{n+1}/L·V_n) ⊗ (ℚL)^*`. -/
def residueFiberTensorEquiv (n : ℕ) (H : Normal) :
    ResidueFiber n H ≃ₗ[ℚ]
      quotLin n (equation H) ⊗[ℚ] Module.Dual ℚ (Submodule.span ℚ {equation H}) :=
  (fibreEquiv n H).trans (residueTensorEquiv n (equation H) (equation_ne_zero H))

/-- The library residue of `(0, single H q)` at `H` is the class of `q`. -/
theorem residue_component_fraction (n : ℕ) (H : Normal) (q : V (n+1)) :
    residue n ((presentationMap n).rangeRestrict (0, DFinsupp.single H q)) H =
      (numeratorRelations n H).mkQ q := by
  rw [residue_presentation]
  have h := numeratorResidues_apply n (DFinsupp.single H q) H
  rw [DFinsupp.single_eq_same] at h
  exact h

/-- The residue of the fraction `q/L` under the isomorphism is `[q] ⊗ L^∨`. -/
theorem residue_fraction_tensor (n : ℕ) (H : Normal) (q : V (n+1)) :
    residueFiberTensorEquiv n H
        (residue n ((presentationMap n).rangeRestrict (0, DFinsupp.single H q)) H) =
      (Submodule.Quotient.mk q : quotLin n (equation H)) ⊗ₜ[ℚ] lineDual (equation H) (equation_ne_zero H) := by
  rw [residue_component_fraction]
  change residueTensorEquiv n (equation H) (equation_ne_zero H)
      (Submodule.quotEquivOfEq _ _ (numeratorRelations_eq n H) (Submodule.Quotient.mk q)) = _
  rw [Submodule.quotEquivOfEq_mk]
  exact toTensor_apply _ _ _ _

/-- Scaling `L` by `c` does not change the line: `ℚ(cL) ⊇ ℚL`. -/
theorem span_scale (c : ℚ) (hc : c ≠ 0) (L : V 1) :
    Submodule.span ℚ {c • L} = Submodule.span ℚ {L} :=
  Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc) L

theorem mulLin_smul (n : ℕ) (c : ℚ) (L : V 1) (p : V n) :
    mulLin n (c • L) p = c • mulLin n L p :=
  Subtype.ext (by
    change (c • L.val) * p.val = c • (L.val * p.val)
    exact smul_mul_assoc _ _ _)

theorem range_mulLin_smul (n : ℕ) {c : ℚ} (hc : c ≠ 0) (L : V 1) :
    LinearMap.range (mulLin n (c • L)) = LinearMap.range (mulLin n L) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨c • p, by rw [map_smul, mulLin_smul]⟩
  · rintro ⟨p, rfl⟩
    refine ⟨c⁻¹ • p, ?_⟩
    rw [mulLin_smul, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- The canonical identification `V_{n+1}/cL·V_n ≅ V_{n+1}/L·V_n`. -/
def quotEquivScale (n : ℕ) {c : ℚ} (hc : c ≠ 0) (L : V 1) :
    quotLin n (c • L) ≃ₗ[ℚ] quotLin n L :=
  Submodule.quotEquivOfEq _ _ (range_mulLin_smul n hc L)

theorem quotEquivScale_mk (n : ℕ) {c : ℚ} (hc : c ≠ 0) (L : V 1) (x : V (n+1)) :
    quotEquivScale n hc L (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  simp [quotEquivScale]

theorem scale_ne_zero (c : ℚ) (hc : c ≠ 0) (L : V 1) (hL : L ≠ 0) : c • L ≠ 0 :=
  fun h => hL ((smul_eq_zero.mp h).resolve_left hc)

/-- The inclusion of the line `ℚL` into `ℚ(cL)`. -/
theorem span_le_scale (c : ℚ) (hc : c ≠ 0) (L : V 1) :
    Submodule.span ℚ {L} ≤ Submodule.span ℚ {c • L} :=
  (span_scale c hc L).symm.le

theorem inclusion_mk (c : ℚ) (hc : c ≠ 0) (L : V 1) :
    Submodule.inclusion (span_le_scale c hc L) ⟨L, Submodule.mem_span_singleton_self L⟩ =
      c⁻¹ • (⟨c • L, Submodule.mem_span_singleton_self (c • L)⟩ :
        Submodule.span ℚ {c • L}) :=
  Subtype.ext (by simp [smul_smul, inv_mul_cancel₀ hc])

/-- The dual of the line `ℚ(cL)`, pulled back to `ℚL`, is `c⁻¹ L^∨`. -/
theorem dualMap_lineDual (c : ℚ) (hc : c ≠ 0) (L : V 1) (hL : L ≠ 0) :
    LinearMap.dualMap (Submodule.inclusion (span_le_scale c hc L))
        (lineDual (c • L) (scale_ne_zero c hc L hL)) = c⁻¹ • lineDual L hL := by
  have key := dual_eq_smul L hL (LinearMap.dualMap (Submodule.inclusion (span_le_scale c hc L))
    (lineDual (c • L) (scale_ne_zero c hc L hL)))
  rw [key, LinearMap.dualMap_apply, inclusion_mk c hc L, map_smul, lineDual_self, smul_eq_mul,
    mul_one]

/-- Replacing `(p, L)` by `(c·p, c·L)` with `c ≠ 0` does not change `[p] ⊗ L^∨`. -/
theorem residue_scale_tensor (n : ℕ) (L : V 1) (hL : L ≠ 0) {c : ℚ} (hc : c ≠ 0) (p : V (n+1)) :
    TensorProduct.map (quotEquivScale n hc L).toLinearMap
        (LinearMap.dualMap (Submodule.inclusion (span_le_scale c hc L)))
        ((Submodule.Quotient.mk (c • p) : quotLin n (c • L)) ⊗ₜ[ℚ]
          lineDual (c • L) (scale_ne_zero c hc L hL)) =
      (Submodule.Quotient.mk p : quotLin n L) ⊗ₜ[ℚ] lineDual L hL := by
  rw [TensorProduct.map_tmul, dualMap_lineDual c hc L hL]
  change quotEquivScale n hc L (Submodule.Quotient.mk (c • p)) ⊗ₜ[ℚ] _ = _
  rw [quotEquivScale_mk n hc L (c • p), Submodule.Quotient.mk_smul, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', smul_smul, inv_mul_cancel₀ hc, one_smul]

end TernaryPeriodPolynomials.Argument.Identities.ResidueTensor
