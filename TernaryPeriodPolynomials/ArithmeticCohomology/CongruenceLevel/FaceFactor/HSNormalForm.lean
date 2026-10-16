module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CohomologyEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.MixedNormalForm

@[expose] public section


/-!
# Hochschild-Serre normal form of a mixed relative two-cocycle: `U = 0`

Formalized by Claude Sonnet 5.5.

For a split extension `N → E → L` with splitting `s`, a representation `W` of `E`, and a class `x` of `H²(E, W)` restricting to zero on `N`, there is a
relative two-cocycle `z` (vanishing on `N × N`) of class `x` with `z(s a, s b) = 0` for all `a, b ∈ L`, provided `H²(L, -) = 0`.
Proof: `U(a, b) = z₀(s a, s b)` is a two-cocycle of `L` with values in `W|_L`; `U = dκ`; the coboundary of `κ ∘ rightHom` (zero on `N`, so relative)
subtracts `U`.  Consequently `a ↦ splitEdgeCycle a z` is a genuine crossed homomorphism `L → Z¹(N, W)` and its class is the edge class.
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

variable {N E L : Type} [Group N] [Group E] [Group L]

/-- **Normal form `U = 0`.** -/
theorem exists_normal_form {extension : GroupExtension N E L} (splitting : extension.Splitting) (W : Rep ℂ E)
    (hvan : ∀ (A : Rep ℂ L) (x : groupCohomology.H2 A), x = 0)
    (x : (twoCohomologyRestriction extension.inl W).ker) :
    ∃ z : relativeTwoCocycles extension.inl W,
      relativeTwoCocycleClass extension.inl W z = x ∧ ∀ a b : L, z.val (splitting a, splitting b) = 0 := by
  obtain ⟨z0, hz0⟩ := relativeTwoCocycleClass_surjective extension.inl extension.inl_injective W x
  let A : Rep ℂ L := Rep.res (splitting : L →* E) W
  let U : groupCohomology.cocycles₂ A := ⟨fun p => z0.val (splitting p.1, splitting p.2), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro g h k
    have := twoCocycle_relation W z0.val (splitting g) (splitting h) (splitting k)
    change z0.val (splitting (g * h), splitting k) + z0.val (splitting g, splitting h) =
      W.ρ (splitting g) (z0.val (splitting h, splitting k)) + z0.val (splitting g, splitting (h * k))
    simpa only [map_mul] using this⟩
  have hU : groupCohomology.H2π A U = 0 := hvan A _
  obtain ⟨κ, hκ⟩ := (groupCohomology.H2π_eq_zero_iff U).1 hU
  have hκU : ∀ a b : L, A.ρ a (κ b) - κ (a * b) + κ a = z0.val (splitting a, splitting b) := by
    intro a b
    exact congrFun hκ (a, b)
  have hκ1 : κ 1 = 0 := by
    have := hκU 1 1
    have h0 : z0.val (splitting 1, splitting 1) = 0 := by
      simpa only [map_one] using relativeTwoCocycle_one_left extension.inl W z0 1
    rw [h0] at this
    simp only [map_one, Module.End.one_apply, mul_one] at this
    simpa using this
  let primitive : E → W := fun e => κ (extension.rightHom e)
  have hprim : ∀ r, primitive (extension.inl r) = (0 : groupCohomology.cocycles₁ (Rep.res extension.inl W)) r := by
    intro r
    change κ (extension.rightHom (extension.inl r)) = 0
    rw [extension.rightHom_inl, hκ1]
  let correction := relativeBoundaryOfRestriction extension.inl W primitive 0 hprim
  refine ⟨z0 - correction, ?_, ?_⟩
  · apply Subtype.ext
    rw [← hz0]
    change groupCohomology.H2π W (z0.val - correction.val) = groupCohomology.H2π W z0.val
    rw [map_sub, relativeBoundaryOfRestriction_H2_zero, sub_zero]
  · intro a b
    change z0.val (splitting a, splitting b) - twoBoundaryCycle W primitive (splitting a, splitting b) = 0
    rw [twoBoundaryCycle_apply]
    change z0.val (splitting a, splitting b) - (W.ρ (splitting a) (κ (extension.rightHom (splitting b))) -
      κ (extension.rightHom (splitting a * splitting b)) + κ (extension.rightHom (splitting a))) = 0
    rw [← map_mul, splitting.rightHom_splitting, splitting.rightHom_splitting, splitting.rightHom_splitting,
      ← hκU a b]
    exact sub_self _

/-- **The edge cycles of a normal-form cocycle form a crossed homomorphism.** -/
theorem splitEdgeCycle_mul_of_normal {extension : GroupExtension N E L} (splitting : extension.Splitting) (W : Rep ℂ E)
    (z : relativeTwoCocycles extension.inl W) (hz : ∀ a b : L, z.val (splitting a, splitting b) = 0) (a b : L) :
    splitEdgeCycle splitting W (a * b) z =
      splitRadicalCocycleAction splitting W a (splitEdgeCycle splitting W b z) + splitEdgeCycle splitting W a z := by
  rw [splitEdgeCycle_mul, hz a b]
  have : oneBoundaryCycle (Rep.res extension.inl W) (0 : W) = 0 := by
    apply groupCohomology.cocycles₁_ext
    intro r
    simp only [oneBoundaryCycle_apply, map_zero, sub_self]
    rfl
  rw [this, add_zero]

/-- **The edge class is the class of the crossed homomorphism `a ↦ [splitEdgeCycle a z]`.** -/
theorem splitCohomologyEdge_of_normal {extension : GroupExtension N E L} (splitting : extension.Splitting) (W : Rep ℂ E)
    (z : relativeTwoCocycles extension.inl W) (hz : ∀ a b : L, z.val (splitting a, splitting b) = 0) :
    (∀ a b : L, splitEdgeCycle splitting W (a * b) z =
      splitRadicalCocycleAction splitting W a (splitEdgeCycle splitting W b z) + splitEdgeCycle splitting W a z) ∧
    (∀ a : L, (splitCocycleEdge splitting W z : L → groupCohomology.H1 (Rep.res extension.inl W)) a =
      groupCohomology.H1π (Rep.res extension.inl W) (splitEdgeCycle splitting W a z)) ∧
    splitCohomologyEdge splitting W (relativeTwoCocycleClass extension.inl W z) =
      groupCohomology.H1π (splitRadicalH1Representation splitting W) (splitCocycleEdge splitting W z) :=
  ⟨splitEdgeCycle_mul_of_normal splitting W z hz, fun a => splitCocycleEdge_apply splitting W z a,
    splitCohomologyEdge_apply splitting W z⟩

/-- **The edge class of a class `x` in the kernel of the radical restriction, via a genuine crossed homomorphism.** -/
theorem exists_crossed_edge {extension : GroupExtension N E L} (splitting : extension.Splitting) (W : Rep ℂ E)
    (hvan : ∀ (A : Rep ℂ L) (x : groupCohomology.H2 A), x = 0)
    (x : (twoCohomologyRestriction extension.inl W).ker) :
    ∃ c : L → groupCohomology.cocycles₁ (Rep.res extension.inl W),
      (∀ a b : L, c (a * b) = splitRadicalCocycleAction splitting W a (c b) + c a) ∧
      splitCohomologyEdge splitting W x =
        groupCohomology.H1π (splitRadicalH1Representation splitting W)
          (splitCocycleEdge splitting W (Classical.choose (exists_normal_form splitting W hvan x))) ∧
      ∀ a, (splitCocycleEdge splitting W (Classical.choose (exists_normal_form splitting W hvan x)) :
          L → groupCohomology.H1 (Rep.res extension.inl W)) a =
        groupCohomology.H1π (Rep.res extension.inl W) (c a) := by
  obtain ⟨hclass, hz⟩ := Classical.choose_spec (exists_normal_form splitting W hvan x)
  set z := Classical.choose (exists_normal_form splitting W hvan x)
  obtain ⟨h1, h2, h3⟩ := splitCohomologyEdge_of_normal splitting W z hz
  refine ⟨fun a => splitEdgeCycle splitting W a z, h1, ?_, h2⟩
  rw [← hclass]
  exact h3

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
