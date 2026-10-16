module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSMixedNormalForm

@[expose] public section


/-!
# The explicit primitive of a normal-form cocycle on a cusp-stabilizer flag group

Formalized by Claude Sonnet 5.5.

Let `z` be a relative two-cocycle with `z(s a, s b) = 0` and `z(inl r, s l) = 0` (`exists_normal_form_mixed`), `M ≤ L` a subgroup (a cusp stabilizer) and
`B = rightHom⁻¹ M ⊇ inl N` the flag group.  Write `c̃(a) = splitEdgeCycle a z` (the crossed edge).  Given data `φ ∈ Z¹(N, W)` and `χ : L → W`
crossed on `M` (`χ(ab) = s(a)·χ(b) + χ(a)`) with `c̃(a) = a·φ - φ - dχ(a)` for `a ∈ M` (for a cyclic `M = ⟨σ⟩` this is
`c̃(σ) = (σ-1)φ + dε` with `ε = -χ(σ)`), the 1-cochain
`flagPrimitive φ χ (inl r · s a) = φ(r) + inl(r)·χ(a)`
is a primitive of `z` on `B`: `z(e₁, e₂) = e₁·w(e₂) - w(e₁e₂) + w(e₁)` for `e₁, e₂ ∈ B` (`flag_primitive_of_crossed`).
Conversely a primitive on `B` gives such data (`flag_data_of_primitive`).
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

variable {N E L : Type} [Group N] [Group E] [Group L] {extension : GroupExtension N E L}
  (splitting : extension.Splitting) (W : Rep ℂ E)

/-- **The explicit flag primitive**: `w(inl r · s a) = φ(r) + inl(r)·χ(a)`. -/
def flagPrimitive (φ : groupCohomology.cocycles₁ (Rep.res extension.inl W)) (χ : L → W) (e : E) : W :=
  φ (splitRadicalCoordinate splitting e) +
    W.ρ (extension.inl (splitRadicalCoordinate splitting e)) (χ (extension.rightHom e))

theorem flagPrimitive_pair (φ : groupCohomology.cocycles₁ (Rep.res extension.inl W)) (χ : L → W) (r : N) (a : L) :
    flagPrimitive splitting W φ χ (extension.inl r * splitting a) =
      φ r + W.ρ (extension.inl r) (χ a) := by
  unfold flagPrimitive
  rw [splitRadicalCoordinate_pair, map_mul, extension.rightHom_inl, splitting.rightHom_splitting, one_mul]

/-- The value of a normal-form cocycle on a pair `(inl r₁ · s a, s a⁻¹-transported ...)` is the crossed edge. -/
theorem normal_pair_value (z : relativeTwoCocycles extension.inl W) (hU : ∀ a b : L, z.val (splitting a, splitting b) = 0)
    (hmix : ∀ (r : N) (l : L), z.val (extension.inl r, splitting l) = 0) (r1 r : N) (a b : L) :
    z.val (extension.inl r1 * splitting a,
      extension.inl (splitRadicalInput splitting a r) * splitting b) =
      W.ρ (extension.inl r1) (splitEdgeCycle splitting W a z r) := by
  have hl := relativeTwoCocycle_radical_left splitting W z hmix
  have e1 := twoCocycle_relation W z.val (extension.inl r1) (splitting a)
    (extension.inl (splitRadicalInput splitting a r) * splitting b)
  simp only [hmix, hl, add_zero] at e1
  rw [e1]
  congr 1
  have e2 := twoCocycle_relation W z.val (splitting a) (extension.inl (splitRadicalInput splitting a r)) (splitting b)
  rw [← splitRadicalInput_commute splitting a r] at e2
  have e3 := twoCocycle_relation W z.val (extension.inl r) (splitting a) (splitting b)
  simp only [hmix, hU, hl, map_zero, add_zero] at e3
  rw [e3] at e2
  simp only [hmix, map_zero, zero_add] at e2
  rw [splitEdgeCycle_apply, hmix, sub_zero]
  exact e2.symm

/-- **The flag primitive** (`M3b(ii)`): a normal-form cocycle is the coboundary of `flagPrimitive` on the flag group `rightHom⁻¹ M`. -/
theorem flag_primitive_of_crossed (z : relativeTwoCocycles extension.inl W)
    (hU : ∀ a b : L, z.val (splitting a, splitting b) = 0)
    (hmix : ∀ (r : N) (l : L), z.val (extension.inl r, splitting l) = 0) (M : Subgroup L)
    (φ : groupCohomology.cocycles₁ (Rep.res extension.inl W)) (χ : L → W)
    (hχ : ∀ a ∈ M, ∀ b ∈ M, χ (a * b) = W.ρ (splitting a) (χ b) + χ a)
    (hc : ∀ a ∈ M, splitEdgeCycle splitting W a z =
      splitRadicalCocycleAction splitting W a φ - φ - oneBoundaryCycle (Rep.res extension.inl W) (χ a))
    (e₁ e₂ : E) (h₁ : extension.rightHom e₁ ∈ M) (h₂ : extension.rightHom e₂ ∈ M) :
    z.val (e₁, e₂) = W.ρ e₁ (flagPrimitive splitting W φ χ e₂) - flagPrimitive splitting W φ χ (e₁ * e₂) +
      flagPrimitive splitting W φ χ e₁ := by
  obtain ⟨r1, a, rfl⟩ := split_exists_pair splitting e₁
  obtain ⟨r2, b, rfl⟩ := split_exists_pair splitting e₂
  obtain ⟨r, rfl⟩ : ∃ r, splitRadicalInput splitting a r = r2 := (splitting.conjAct a⁻¹).surjective r2
  have haM : a ∈ M := by
    rwa [map_mul, extension.rightHom_inl, splitting.rightHom_splitting, one_mul] at h₁
  have hbM : b ∈ M := by
    rwa [map_mul, extension.rightHom_inl, splitting.rightHom_splitting, one_mul] at h₂
  have hprod : extension.inl r1 * splitting a * (extension.inl (splitRadicalInput splitting a r) * splitting b) =
      extension.inl (r1 * r) * splitting (a * b) := by
    calc _ = extension.inl r1 * (splitting a * extension.inl (splitRadicalInput splitting a r)) * splitting b := by
          simp only [mul_assoc]
      _ = extension.inl r1 * (extension.inl r * splitting a) * splitting b := by
          rw [← splitRadicalInput_commute]
      _ = _ := by rw [map_mul, map_mul]; simp only [mul_assoc]
  rw [hprod, flagPrimitive_pair, flagPrimitive_pair, flagPrimitive_pair, normal_pair_value splitting W z hU hmix r1 r a b,
    hc a haM]
  have F1 := (groupCohomology.mem_cocycles₁_iff _).1 φ.property r1 r
  have F2 := hχ a haM b hbM
  have F3 : ∀ v, W.ρ (splitting a) (W.ρ (extension.inl (splitRadicalInput splitting a r)) v) =
      W.ρ (extension.inl r) (W.ρ (splitting a) v) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, ← splitRadicalInput_commute, map_mul, Module.End.mul_apply]
  change φ (r1 * r) = W.ρ (extension.inl r1) (φ r) + φ r1 at F1
  rw [map_mul, Module.End.mul_apply, map_add (W.ρ (splitting a)), F3, F2, F1,
    map_mul extension.inl r1 r, map_mul (W.ρ) (extension.inl r1) (extension.inl r), Module.End.mul_apply]
  have hsub : ∀ (x y : groupCohomology.cocycles₁ (Rep.res extension.inl W)) (q : N), (x - y) q = x q - y q :=
    fun x y q => rfl
  rw [hsub, hsub, splitRadicalCocycleAction_apply, oneBoundaryCycle_apply]
  simp only [map_add, map_sub]
  simp only [MonoidHom.comp_apply]
  abel

/-- **Converse**: a primitive `w₀` of `z` on the flag group gives the data `(φ, χ) = (w₀ ∘ inl, w₀ ∘ s)` (so mixedness at the flag
is equivalent to the existence of such data). -/
theorem flag_data_of_primitive (z : relativeTwoCocycles extension.inl W)
    (hU : ∀ a b : L, z.val (splitting a, splitting b) = 0) (M : Subgroup L) (w₀ : E → W)
    (hw₀ : ∀ e₁ e₂ : E, extension.rightHom e₁ ∈ M → extension.rightHom e₂ ∈ M →
      z.val (e₁, e₂) = W.ρ e₁ (w₀ e₂) - w₀ (e₁ * e₂) + w₀ e₁) :
    ∃ (φ : groupCohomology.cocycles₁ (Rep.res extension.inl W)) (χ : L → W),
      (∀ r, φ r = w₀ (extension.inl r)) ∧ (∀ a, χ a = w₀ (splitting a)) ∧
      (∀ a ∈ M, ∀ b ∈ M, χ (a * b) = W.ρ (splitting a) (χ b) + χ a) ∧
      ∀ a ∈ M, splitEdgeCycle splitting W a z =
        splitRadicalCocycleAction splitting W a φ - φ - oneBoundaryCycle (Rep.res extension.inl W) (χ a) := by
  have hN1 : ∀ r : N, extension.rightHom (extension.inl r) ∈ M := fun r => by
    rw [extension.rightHom_inl]; exact M.one_mem
  have hS : ∀ a ∈ M, extension.rightHom (splitting a) ∈ M := fun a ha => by
    rw [splitting.rightHom_splitting]; exact ha
  refine ⟨⟨fun r => w₀ (extension.inl r), ?_⟩, fun a => w₀ (splitting a), fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro r1 r2
    have := hw₀ (extension.inl r1) (extension.inl r2) (hN1 r1) (hN1 r2)
    rw [z.property r1 r2, ← map_mul] at this
    change w₀ (extension.inl (r1 * r2)) = W.ρ (extension.inl r1) (w₀ (extension.inl r2)) + w₀ (extension.inl r1)
    rw [map_mul]
    rw [map_mul] at this
    linear_combination (norm := abel) this
  · intro a ha b hb
    have := hw₀ (splitting a) (splitting b) (hS a ha) (hS b hb)
    rw [hU a b, ← map_mul] at this
    change w₀ (splitting (a * b)) = W.ρ (splitting a) (w₀ (splitting b)) + w₀ (splitting a)
    linear_combination (norm := abel) this
  · intro a ha
    apply groupCohomology.cocycles₁_ext
    intro r
    have h1 := hw₀ (splitting a) (extension.inl (splitRadicalInput splitting a r)) (hS a ha) (hN1 _)
    have h2 := hw₀ (extension.inl r) (splitting a) (hN1 r) (hS a ha)
    rw [← splitRadicalInput_commute] at h1
    have hsub : ∀ (x y : groupCohomology.cocycles₁ (Rep.res extension.inl W)) (q : N), (x - y) q = x q - y q :=
      fun x y q => rfl
    rw [splitEdgeCycle_apply, hsub, hsub, splitRadicalCocycleAction_apply, oneBoundaryCycle_apply, h1, h2]
    change _ = W.ρ (splitting a) (w₀ (extension.inl (splitRadicalInput splitting a r))) - w₀ (extension.inl r) -
      (W.ρ (extension.inl r) (w₀ (splitting a)) - w₀ (splitting a))
    abel

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
