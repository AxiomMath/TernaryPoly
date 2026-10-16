module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.PlaneTransfer

@[expose] public section


/-!
# The single-element Hecke scalar `ω(B)` away from three

For `B ∈ GL₂(𝔸_f)` trivial at three, the compression of `σ(B)` to the `GL₂(Ẑ^{(3)})`-fixed
vectors is a scalar `ω(B)`. It depends only on the double coset of `B` and is invariant under
transposition. A fixed combination `∑ cᵢ σ(Bᵢ) w` therefore equals `(∑ cᵢ ω(Bᵢ)) w`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.RepresentationTheory

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

/-- The scalar of an operator which is a scalar on a nontrivial space (zero otherwise). -/
def scalarOf {E : Type*} [AddCommGroup E] [Module ℂ E] (T : E → E) : ℂ :=
  open Classical in
  if h : Nontrivial E ∧ ∃ z : ℂ, ∀ w, T w = z • w then h.2.choose else 0

theorem scalarOf_spec {E : Type*} [AddCommGroup E] [Module ℂ E] (T : E → E)
    (h : ∃ z : ℂ, ∀ w, T w = z • w) : ∀ w, T w = scalarOf T • w := by
  intro w
  rcases subsingleton_or_nontrivial E with hs | hn
  · exact Subsingleton.elim _ _
  · have hh : Nontrivial E ∧ ∃ z : ℂ, ∀ w, T w = z • w := ⟨hn, h⟩
    rw [scalarOf, dite_eq_left hh]
    exact hh.2.choose_spec w

/-- The away-from-three level inside `GL₂(𝔸)`. -/
abbrev K3 : Subgroup BinaryAdelicGL := awayLevelA placeThree

/-- **`ω(B)`**: the scalar of the compression of `σ(B)`. -/
def omega (σ : CuspidalRepresentation) (B : BinaryFiniteGL) : ℂ :=
  scalarOf (compression σ K3 (atFinite B))

theorem compression_scalar (σ : CuspidalRepresentation) {B : BinaryFiniteGL}
    (hB : B ∈ awayGroup placeThree) :
    ∃ z : ℂ, ∀ w, compression σ K3 (atFinite B) w = z • w := by
  have hK' : ∀ k ∈ (⊥ : Subgroup BinaryAdelicGL), ∀ y ∈ awayGroupA placeThree,
      k * y = y * k := by
    intro k hk y _; rw [Subgroup.mem_bot.mp hk, one_mul, mul_one]
  obtain ⟨z, hz⟩ := awayCombination_scalar σ ⊥ hK' ({()} : Finset Unit) (fun _ => 1)
    (fun _ => B) (fun _ _ => hB)
  have hK : awayLevelA placeThree ⊔ ⊥ = awayLevelA placeThree := sup_bot_eq _
  rw [hK] at hz
  refine ⟨z, fun w => ?_⟩
  have := hz w
  simpa using this

theorem omega_spec (σ : CuspidalRepresentation) {B : BinaryFiniteGL}
    (hB : B ∈ awayGroup placeThree) (w : fixedVectors σ K3) :
    compression σ K3 (atFinite B) w = omega σ B • w :=
  scalarOf_spec _ (compression_scalar σ hB) w

/-- Compressions are invariant under the level on both sides. -/
theorem compression_level (σ : CuspidalRepresentation) (g : BinaryAdelicGL) {a b : BinaryAdelicGL}
    (ha : a ∈ K3) (hb : b ∈ K3) :
    compression σ K3 (a * g * b) = compression σ K3 g := by
  refine ContinuousLinearMap.ext fun v => ?_
  apply ext_inner_right ℂ
  intro w
  rw [inner_compression, inner_compression]
  have hv : σ.π b (v : σ.H) = v := v.property ⟨b, hb⟩
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hv]
  exact inner_pi_fixed σ ⟨a, ha⟩ _ w.property

theorem atFinite_mem_K3 {k : BinaryFiniteGL} (hk : k ∈ awayLevel placeThree) : atFinite k ∈ K3 :=
  ⟨k, hk, rfl⟩

theorem omega_level (σ : CuspidalRepresentation) (B : BinaryFiniteGL) {a b : BinaryFiniteGL}
    (ha : a ∈ awayLevel placeThree) (hb : b ∈ awayLevel placeThree) :
    omega σ (a * B * b) = omega σ B := by
  unfold omega
  rw [← HeckeTranslate.HeckeInvariance.atFinite_mul, ← HeckeTranslate.HeckeInvariance.atFinite_mul,
    compression_level σ _ (atFinite_mem_K3 ha) (atFinite_mem_K3 hb)]

theorem omega_transpose (σ : CuspidalRepresentation) {B : BinaryFiniteGL}
    (hB : B ∈ awayGroup placeThree) : omega σ (transposeGL B) = omega σ B := by
  obtain ⟨a, b, hab⟩ := away_transpose_cartan hB
  rw [hab, omega_level σ B a.property b.property]

/-- **A fixed combination is the `ω`-weighted scalar.** -/
theorem fixed_combination_omega (σ : CuspidalRepresentation) {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (x : ι → BinaryFiniteGL) (hx : ∀ i ∈ S, x i ∈ awayGroup placeThree)
    (w : σ.H) (hw : w ∈ fixedVectors σ K3)
    (hsum : (∑ i ∈ S, c i • σ.π (atFinite (x i)) w) ∈ fixedVectors σ K3) :
    ∑ i ∈ S, c i • σ.π (atFinite (x i)) w = (∑ i ∈ S, c i * omega σ (x i)) • w := by
  have hproj : (fixedVectors σ K3).starProjection (∑ i ∈ S, c i • σ.π (atFinite (x i)) w) =
      ∑ i ∈ S, c i • σ.π (atFinite (x i)) w :=
    Submodule.starProjection_eq_self_iff.mpr hsum
  rw [← hproj, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, mul_smul]
  congr 1
  have h := congrArg Subtype.val (omega_spec σ (hx i hi) ⟨w, hw⟩)
  rw [compression_coe] at h
  exact h

end TernaryPeriodPolynomials.HeckeEigen.Satake
