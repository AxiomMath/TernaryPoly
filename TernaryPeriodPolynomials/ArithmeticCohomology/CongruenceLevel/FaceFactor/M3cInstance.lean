module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Sum7
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSFlagPrimitive

@[expose] public section


/-!
# M3c(iii) instantiation: the seven-term sum of `flagPrimitive ∪ (normal-form cocycle)`

Formalized by Claude Sonnet 5.5.  Joins `GammaNFaceFactor.HSFlagPrimitive` with the `FlagH3.Sum7`.

Frame (`FlagCohomDatum` side): `X = inl x₀` (radical), `Y = s σ`, `W = [X, Y] = inl w₀`.  Hypotheses used, all about the extension `1 → N → E → L → 1` with Levi splitting `s`:
* `hcomm`: the radical `N` is commutative;
* `hw₀ : inl w₀ = [inl x₀, s σ]` (`exists_comm_radical` produces `w₀`: the commutator is in `ker rightHom = inl N`);
* `hfix : inl w₀ * s σ = s σ * inl w₀` (`W` commutes with `Y`, i.e. `σ` fixes `w₀`; unipotent frame);
* `z'` a normal-form relative cocycle (`exists_normal_form_mixed`): `z'(s a, s b) = 0`, `z'(inl r, s l) = 0`;
* `φ ∈ Z¹(N, W)`, `χ : L → W` with `χ 1 = 0`; `u = flagPrimitive φ χ`.
`sum7_cup12_normal_form`: `Σ7(u ∪ z') = e(φ x₀)(ρ'(inl(x₀ w₀⁻¹))(c w₀)) - e(φ w₀)(c x₀)`, `c = splitEdgeCycle σ z'`.
`sum7_cup21_normal_form` (planes): `Σ7(z ∪ w) = e(c(w₀))(ρ'(s σ · inl w₀)(φ' x₀)) - e(c(w₀⁻¹ x₀))(ρ'(s σ · inl x₀)(φ' w₀))`.
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.FlagH3

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

section Sum7Radical

variable {B : Type} [Group B]

/-- `FlagH3.sum7_cup12_flag` with the cocycle law for `κ'` assumed only on a subgroup `S` containing `X` and `W` (the radical). -/
theorem sum7_cup12_flag_radical {V W' : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W'] [Module ℚ W']
    (ρ' : Representation ℚ B W') (e : V →ₗ[ℚ] W' →ₗ[ℚ] ℚ) (X Y : B) (S : Subgroup B) (hX : X ∈ S)
    (hW : comm X Y ∈ S) (u : B → V) (β : B → B → W') (κ' : B → W')
    (hβX : ∀ g, β X g = 0) (hβW : ∀ g, β (comm X Y) g = 0)
    (hκ : ∀ a ∈ S, ∀ b ∈ S, κ' (a * b) = κ' a + ρ' a (κ' b))
    (hβYX : β Y X = κ' ((comm X Y)⁻¹ * X))
    (hβY'W : β (X⁻¹ * Y * X) (comm X Y) = ρ' (comm X Y)⁻¹ (κ' (comm X Y))) :
    sum7 X Y (cup12 ρ' e u β) =
      e (u X) (ρ' (X * (comm X Y)⁻¹) (κ' (comm X Y))) - e (u (comm X Y)) (κ' X) := by
  have k1 : κ' 1 = 0 := by
    have := hκ 1 S.one_mem 1 S.one_mem
    simp only [mul_one, map_one, Module.End.one_apply] at this
    exact left_eq_add.mp this
  have kinv : ρ' (comm X Y) (κ' (comm X Y)⁻¹) = - κ' (comm X Y) := by
    have := hκ (comm X Y) hW (comm X Y)⁻¹ (S.inv_mem hW)
    rw [mul_inv_cancel, k1] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have kXW : ρ' (comm X Y) (κ' ((comm X Y)⁻¹ * X)) = κ' X - κ' (comm X Y) := by
    rw [hκ _ (S.inv_mem hW) _ hX, map_add, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply, kinv]
    abel
  have kXW' : ρ' (comm X Y) (ρ' (comm X Y)⁻¹ (κ' (comm X Y))) = κ' (comm X Y) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  unfold sum7 cup12
  rw [hβX, hβX, hβW, hβW, hβY'W, hβYX]
  simp only [map_zero, kXW, kXW', map_sub, map_mul, Module.End.mul_apply]
  abel

end Sum7Radical

section Frame

variable {N E L : Type} [Group N] [Group E] [Group L] {extension : GroupExtension N E L}
  (splitting : extension.Splitting)

/-- The commutator `[inl x₀, s σ]` is a radical element. -/
theorem exists_comm_radical (x₀ : N) (σ : L) :
    ∃ w₀ : N, extension.inl w₀ = comm (extension.inl x₀) (splitting σ) := by
  have h : comm (extension.inl x₀) (splitting σ) ∈ extension.rightHom.ker := by
    rw [MonoidHom.mem_ker]
    simp only [FlagH3.comm, map_mul, map_inv, extension.rightHom_inl, splitting.rightHom_splitting]
    group
  rw [← extension.range_inl_eq_ker_rightHom] at h
  exact h

variable {splitting}

/-- If `inl r * s a = s a * inl x` then `a · r = x`. -/
theorem radicalInput_eq_of_commute (a : L) (r x : N)
    (h : extension.inl r * splitting a = splitting a * extension.inl x) : splitRadicalInput splitting a r = x := by
  have h2 := splitRadicalInput_commute splitting a r
  rw [h2] at h
  exact extension.inl_injective (mul_left_cancel h)

section Instance

theorem frame_conj {x₀ w₀ : N} {σ : L} (hw₀ : extension.inl w₀ = FlagH3.comm (extension.inl x₀) (splitting σ)) :
    splitting σ * extension.inl x₀ = extension.inl (w₀⁻¹ * x₀) * splitting σ := by
  rw [map_mul, map_inv, hw₀]
  simp only [FlagH3.comm]
  group

/-- `z'(s σ, inl x₀) = c(w₀⁻¹ x₀)` for `c = splitEdgeCycle σ z'`. -/
theorem normal_Y_X (W' : Rep ℂ E) (z' : relativeTwoCocycles extension.inl W')
    (hmix : ∀ (r : N) (l : L), z'.val (extension.inl r, splitting l) = 0) {x₀ w₀ : N} {σ : L}
    (hw₀ : extension.inl w₀ = FlagH3.comm (extension.inl x₀) (splitting σ)) :
    z'.val (splitting σ, extension.inl x₀) = splitEdgeCycle splitting W' σ z' (w₀⁻¹ * x₀) := by
  have h := radicalInput_eq_of_commute σ (w₀⁻¹ * x₀) x₀ (frame_conj hw₀).symm
  rw [splitEdgeCycle_apply, h, hmix, sub_zero]

/-- `z'(X⁻¹ Y X, W) = W⁻¹ · c(W)`. -/
theorem normal_Y'_W (W' : Rep ℂ E) (z' : relativeTwoCocycles extension.inl W')
    (hU : ∀ a b : L, z'.val (splitting a, splitting b) = 0)
    (hmix : ∀ (r : N) (l : L), z'.val (extension.inl r, splitting l) = 0) (hcomm : ∀ a b : N, a * b = b * a)
    {x₀ w₀ : N} {σ : L} (hw₀ : extension.inl w₀ = FlagH3.comm (extension.inl x₀) (splitting σ))
    (hfix : extension.inl w₀ * splitting σ = splitting σ * extension.inl w₀) :
    z'.val (extension.inl x₀⁻¹ * splitting σ * extension.inl x₀, extension.inl w₀) =
      W'.ρ (extension.inl w₀⁻¹) (splitEdgeCycle splitting W' σ z' w₀) := by
  have e1 : extension.inl x₀⁻¹ * splitting σ * extension.inl x₀ = extension.inl w₀⁻¹ * splitting σ := by
    rw [mul_assoc, frame_conj hw₀, ← mul_assoc, ← map_mul]
    congr 2
    rw [← mul_assoc, hcomm x₀⁻¹ w₀⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have e2 : extension.inl w₀ = extension.inl (splitRadicalInput splitting σ w₀) * splitting 1 := by
    rw [radicalInput_eq_of_commute σ w₀ w₀ hfix, map_one, mul_one]
  rw [e1]
  conv_lhs => rw [e2]
  exact normal_pair_value splitting W' z' hU hmix w₀⁻¹ w₀ σ 1

end Instance

section Main

theorem flagPrimitive_inl (W : Rep ℂ E) (φ : groupCohomology.cocycles₁ (Rep.res extension.inl W)) (χ : L → W)
    (hχ1 : χ 1 = 0) (r : N) : flagPrimitive splitting W φ χ (extension.inl r) = φ r := by
  unfold flagPrimitive
  rw [splitRadicalCoordinate_inl, extension.rightHom_inl, hχ1, map_zero, add_zero]

/-- **M3c(iii), lines: `Σ7(flagPrimitive ∪ z')` in closed form.** -/
theorem sum7_cup12_normal_form (W W' : Rep ℂ E) [Module ℚ W] [Module ℚ W'] (ρ' : Representation ℚ E W')
    (hρ' : ∀ g x, ρ' g x = W'.ρ g x) (e : W →ₗ[ℚ] W' →ₗ[ℚ] ℚ) (z' : relativeTwoCocycles extension.inl W')
    (hU : ∀ a b : L, z'.val (splitting a, splitting b) = 0)
    (hmix : ∀ (r : N) (l : L), z'.val (extension.inl r, splitting l) = 0) (hcomm : ∀ a b : N, a * b = b * a)
    {x₀ w₀ : N} {σ : L} (hw₀ : extension.inl w₀ = FlagH3.comm (extension.inl x₀) (splitting σ))
    (hfix : extension.inl w₀ * splitting σ = splitting σ * extension.inl w₀)
    (φ : groupCohomology.cocycles₁ (Rep.res extension.inl W)) (χ : L → W) (hχ1 : χ 1 = 0) :
    sum7 (extension.inl x₀) (splitting σ)
        (cup12 ρ' e (flagPrimitive splitting W φ χ) (fun a b => z'.val (a, b))) =
      e (φ x₀) (ρ' (extension.inl (x₀ * w₀⁻¹)) (splitEdgeCycle splitting W' σ z' w₀)) -
        e (φ w₀) (splitEdgeCycle splitting W' σ z' x₀) := by
  have hl := relativeTwoCocycle_radical_left splitting W' z' hmix
  have key := sum7_cup12_flag_radical ρ' e (extension.inl x₀) (splitting σ) extension.inl.range ⟨x₀, rfl⟩
    (by rw [← hw₀]; exact ⟨w₀, rfl⟩) (flagPrimitive splitting W φ χ) (fun a b => z'.val (a, b))
    (fun g => splitEdgeCycle splitting W' σ z' (splitRadicalCoordinate splitting g)) (fun g => hl x₀ g)
    (fun g => by rw [← hw₀]; exact hl w₀ g)
    (by
      rintro _ ⟨r1, rfl⟩ _ ⟨r2, rfl⟩
      rw [← map_mul]
      simp only [splitRadicalCoordinate_inl, hρ']
      exact (groupCohomology.mem_cocycles₁_iff _).1 (splitEdgeCycle splitting W' σ z').property r1 r2 |>.trans (add_comm _ _))
    (by
      rw [← hw₀, ← map_inv, ← map_mul, splitRadicalCoordinate_inl]
      exact normal_Y_X W' z' hmix hw₀)
    (by
      rw [← hw₀, ← map_inv, splitRadicalCoordinate_inl, hρ', ← map_inv]
      exact normal_Y'_W W' z' hU hmix hcomm hw₀ hfix)
  rw [← hw₀, flagPrimitive_inl W φ χ hχ1, flagPrimitive_inl W φ χ hχ1,
    ← map_inv, ← map_mul, splitRadicalCoordinate_inl, splitRadicalCoordinate_inl] at key
  exact key

/-- **M3c(iii), planes: `Σ7(z ∪ flagPrimitive)` in closed form** (`z` normal form with coefficients `V`, the primitive `w = flagPrimitive φ' χ'` with coefficients `W'`). -/
theorem sum7_cup21_normal_form (V W' : Rep ℂ E) [Module ℚ V] [Module ℚ W'] (ρ' : Representation ℚ E W')
    (e : V →ₗ[ℚ] W' →ₗ[ℚ] ℚ) (z : relativeTwoCocycles extension.inl V)
    (hmix : ∀ (r : N) (l : L), z.val (extension.inl r, splitting l) = 0)
    {x₀ w₀ : N} {σ : L} (hw₀ : extension.inl w₀ = FlagH3.comm (extension.inl x₀) (splitting σ))
    (hfix : extension.inl w₀ * splitting σ = splitting σ * extension.inl w₀)
    (φ' : groupCohomology.cocycles₁ (Rep.res extension.inl W')) (χ' : L → W') (hχ1 : χ' 1 = 0) :
    sum7 (extension.inl x₀) (splitting σ)
        (cup21 ρ' e (fun a b => z.val (a, b)) (flagPrimitive splitting W' φ' χ')) =
      e (splitEdgeCycle splitting V σ z w₀) (ρ' (splitting σ * extension.inl w₀) (φ' x₀)) -
        e (splitEdgeCycle splitting V σ z (w₀⁻¹ * x₀)) (ρ' (splitting σ * extension.inl x₀) (φ' w₀)) := by
  have hl := relativeTwoCocycle_radical_left splitting V z hmix
  have key := sum7_cup21_flag ρ' e (extension.inl x₀) (splitting σ) (fun a b => z.val (a, b))
    (flagPrimitive splitting W' φ' χ')
    (fun g => splitEdgeCycle splitting V σ z (splitRadicalCoordinate splitting g)) (fun g => hl x₀ g)
    (fun g => by rw [← hw₀]; exact hl w₀ g)
    (by
      rw [← hw₀, ← map_inv, ← map_mul, splitRadicalCoordinate_inl]
      exact normal_Y_X V z hmix hw₀)
    (by
      rw [← hw₀, splitRadicalCoordinate_inl, splitEdgeCycle_apply, radicalInput_eq_of_commute σ w₀ w₀ hfix, hmix,
        sub_zero])
  rw [← hw₀, flagPrimitive_inl W' φ' χ' hχ1, flagPrimitive_inl W' φ' χ' hχ1, ← map_inv, ← map_mul,
    splitRadicalCoordinate_inl, splitRadicalCoordinate_inl] at key
  exact key

end Main

end Frame

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
