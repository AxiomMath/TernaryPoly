module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Representation.PlaceHecke

@[expose] public section


/-!
# Hecke operators away from one place

For a finite place `v₀`, let `GL₂(𝔸_f^{v₀})` be the finite adelic matrices whose `v₀`-component
is `1`, and `GL₂(Ẑ^{v₀})` its intersection with `GL₂(Ẑ)`. The transpose is a Gelfand involution
for this pair, with Cartan property and finite double cosets derived from the global ones. Hence
every finite combination of compressions of elements of `GL₂(𝔸_f^{v₀})` acts by a scalar on the
vectors of a `CuspidalRepresentation` fixed by `GL₂(Ẑ^{v₀}) ⊔ K'`, for every `K'` commuting with
`GL₂(𝔸_f^{v₀})` (for instance `K' = ⊥`, or a level at `v₀`).

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.RepresentationTheory

variable (v : FinitePlace)

/-- `GL₂(𝔸_f^{v})`: finite adelic matrices trivial at `v`. -/
def awayGroup : Subgroup BinaryFiniteGL :=
  (GeneralLinearGroup.map (finiteEvaluation v) (n := Fin 2)).ker

/-- `GL₂(Ẑ^{v})`. -/
def awayLevel : Subgroup BinaryFiniteGL := awayGroup v ⊓ sphericalFinite

theorem awayLevel_le_awayGroup : awayLevel v ≤ awayGroup v := inf_le_left

theorem awayLevel_le_spherical : awayLevel v ≤ sphericalFinite := inf_le_right

variable {v}

theorem mem_awayGroup {x : BinaryFiniteGL} :
    x ∈ awayGroup v ↔ GeneralLinearGroup.map (finiteEvaluation v) x = 1 := MonoidHom.mem_ker

/-- The `v`-component of a finite adelic matrix, re-embedded at `v`. -/
def placePart (x : BinaryFiniteGL) : BinaryFiniteGL :=
  finiteAtPlaceGL 2 v (GeneralLinearGroup.map (finiteEvaluation v) x)

theorem placePart_mul (x y : BinaryFiniteGL) :
    placePart (v := v) (x * y) = placePart (v := v) x * placePart (v := v) y := by
  simp only [placePart, map_mul]

theorem placePart_spherical {k : BinaryFiniteGL} (hk : k ∈ sphericalFinite) :
    placePart (v := v) k ∈ sphericalFinite := by
  obtain ⟨k₀, hk₀⟩ := eval_mem_localIntegral (v := v) hk
  rw [placePart, ← hk₀]
  exact finiteAtPlaceGL_integral 2 v k₀

/-- Elements supported at `v` commute with elements trivial at `v`. -/
theorem placeAt_commute_away (a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    {y : BinaryFiniteGL} (hy : y ∈ awayGroup v) :
    finiteAtPlaceGL 2 v a * y = y * finiteAtPlaceGL 2 v a := by
  apply finiteGeneralLinearGroup_ext
  intro w
  rw [map_mul, map_mul]
  by_cases h : w = v
  · subst h; rw [mem_awayGroup.mp hy, one_mul, mul_one]
  · rw [finiteAtPlaceGL_away 2 v a w h, one_mul, mul_one]

theorem mul_placePart_inv_mem (x : BinaryFiniteGL) : (placePart (v := v) x)⁻¹ * x ∈ awayGroup v := by
  rw [mem_awayGroup, map_mul, map_inv, placePart, finiteAtPlaceGL_same, inv_mul_cancel]

theorem transposeGL_awayGroup {y : BinaryFiniteGL} (hy : y ∈ awayGroup v) :
    transposeGL y ∈ awayGroup v := by
  rw [mem_awayGroup, ← transposeGL_map, mem_awayGroup.mp hy]
  apply Units.ext; simp

theorem transposeGL_spherical {k : BinaryFiniteGL} (hk : k ∈ sphericalFinite) :
    transposeGL k ∈ sphericalFinite := by
  obtain ⟨k', rfl⟩ := hk
  exact ⟨transposeGL k', (transposeGL_map _ _).symm⟩

theorem transposeGL_awayLevel {k : BinaryFiniteGL} (hk : k ∈ awayLevel v) :
    transposeGL k ∈ awayLevel v :=
  ⟨transposeGL_awayGroup hk.1, transposeGL_spherical hk.2⟩

/-- **Cartan property away from `v`.** -/
theorem away_transpose_cartan {y : BinaryFiniteGL} (hy : y ∈ awayGroup v) :
    ∃ a b : awayLevel v, transposeGL y = a.val * y * b.val := by
  obtain ⟨a, b, hab⟩ := transpose_cartan y
  set α := placePart (v := v) a.val
  set β := placePart (v := v) b.val
  have hev : GeneralLinearGroup.map (finiteEvaluation v) a.val *
      GeneralLinearGroup.map (finiteEvaluation v) b.val = 1 := by
    have := congrArg (GeneralLinearGroup.map (finiteEvaluation v)) hab
    rw [map_mul, map_mul, mem_awayGroup.mp hy, mul_one, mem_awayGroup.mp (transposeGL_awayGroup hy)]
      at this
    exact this.symm
  have hβα : β * α = 1 := by
    have hev' := mul_eq_one_comm.mp hev
    simp only [β, α, placePart, ← map_mul]
    rw [map_mul, hev', map_one]
  refine ⟨⟨a.val * α⁻¹, mem_awayGroup.mpr ?_, ?_⟩, ⟨β⁻¹ * b.val, mem_awayGroup.mpr ?_, ?_⟩, ?_⟩
  · simp only [α, placePart, map_mul, map_inv, finiteAtPlaceGL_same, mul_inv_cancel]
  · exact sphericalFinite.mul_mem a.property (sphericalFinite.inv_mem (placePart_spherical a.property))
  · simp only [β, placePart, map_mul, map_inv, finiteAtPlaceGL_same, inv_mul_cancel]
  · exact sphericalFinite.mul_mem (sphericalFinite.inv_mem (placePart_spherical b.property)) b.property
  · have hcomm : α⁻¹ * y = y * α⁻¹ := by
      have := placeAt_commute_away (v := v) (GeneralLinearGroup.map (finiteEvaluation v) a.val)⁻¹ hy
      rwa [map_inv] at this
    calc transposeGL y = a.val * y * b.val := hab
      _ = a.val * y * (α⁻¹ * β⁻¹) * b.val := by
          rw [← _root_.mul_inv_rev, hβα, inv_one, mul_one]
      _ = a.val * (y * α⁻¹) * β⁻¹ * b.val := by group
      _ = a.val * (α⁻¹ * y) * β⁻¹ * b.val := by rw [hcomm]
      _ = a.val * α⁻¹ * y * (β⁻¹ * b.val) := by group

/-- **Finiteness of double cosets away from `v`.** -/
theorem awayLevel_finiteQuotient {γ : BinaryFiniteGL} (hγ : γ ∈ awayGroup v) :
    Finite (awayLevel v ⧸ conjIntersection (awayLevel v) γ) := by
  let F : awayLevel v ⧸ conjIntersection (awayLevel v) γ →
      sphericalFinite ⧸ conjIntersection sphericalFinite γ :=
    Quotient.map' (Subgroup.inclusion (awayLevel_le_spherical v)) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      have h := mem_conjIntersection.mp hab
      apply mem_conjIntersection.mpr
      exact awayLevel_le_spherical v h)
  apply Finite.of_injective F
  intro c d hcd
  induction c using Quotient.inductionOn' with | h a => ?_
  induction d using Quotient.inductionOn' with | h b => ?_
  apply Quotient.sound'
  have hcd' : (QuotientGroup.mk (Subgroup.inclusion (awayLevel_le_spherical v) a) :
      sphericalFinite ⧸ conjIntersection sphericalFinite γ) =
      QuotientGroup.mk (Subgroup.inclusion (awayLevel_le_spherical v) b) := hcd
  have hmem := mem_conjIntersection.mp (QuotientGroup.eq.mp hcd')
  rw [QuotientGroup.leftRel_apply]
  apply mem_conjIntersection.mpr
  refine ⟨?_, ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (awayGroup v).mul_mem ((awayGroup v).mul_mem ((awayGroup v).inv_mem hγ)
      ((awayGroup v).mul_mem ((awayGroup v).inv_mem a.property.1) b.property.1)) hγ
  · have h2 := hmem
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] at h2 ⊢
    exact h2

/-- `GL₂(𝔸_f^{v})` and `GL₂(Ẑ^{v})` inside `GL₂(𝔸)`. -/
def awayGroupA (v : FinitePlace) : Subgroup BinaryAdelicGL := (awayGroup v).map atFiniteHom
def awayLevelA (v : FinitePlace) : Subgroup BinaryAdelicGL := (awayLevel v).map atFiniteHom

/-- The double coset of `x ∈ GL₂(𝔸_f^{v})` inside `GL₂(𝔸)`. -/
def awayDoubleCoset {x : BinaryFiniteGL} (hx : x ∈ awayGroup v) : DoubleCoset (awayLevelA v) :=
  haveI := awayLevel_finiteQuotient hx
  (DoubleCoset.ofFinite (awayLevel v) x).map atFiniteHom atFiniteHom_injective

theorem awayDoubleCoset_g {x : BinaryFiniteGL} (hx : x ∈ awayGroup v) :
    (awayDoubleCoset hx).g = atFinite x := rfl

/-- The transpose is a Gelfand involution for `GL₂(Ẑ^{v})`, Cartan on `GL₂(𝔸_f^{v})`. -/
def awayGelfand (v : FinitePlace) : GelfandInvolution (awayLevelA v) where
  ι := transposeGL
  map_mul := transposeGL_mul
  invol := transposeGL_transposeGL
  mem := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨transposeGL k, transposeGL_awayLevel hk, (transposeGL_atFinite k).symm⟩
  F := awayGroupA v
  le := Subgroup.map_mono (awayLevel_le_awayGroup v)
  memF := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨transposeGL y, transposeGL_awayGroup hy, (transposeGL_atFinite y).symm⟩
  cartan := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, b, hab⟩ := away_transpose_cartan hy
    refine ⟨⟨atFinite a.val, ⟨a.val, a.property, rfl⟩⟩, ⟨atFinite b.val, ⟨b.val, b.property, rfl⟩⟩, ?_⟩
    change transposeGL (atFinite y) = atFinite a.val * atFinite y * atFinite b.val
    rw [transposeGL_atFinite, hab, HeckeTranslate.HeckeInvariance.atFinite_mul,
      HeckeTranslate.HeckeInvariance.atFinite_mul]

/-- Every element of `GL₂(𝔸)` is a product of a factor commuting with `GL₂(𝔸_f^{v})` and an
element of `GL₂(𝔸_f^{v})`. -/
theorem away_decomp (h : BinaryAdelicGL) : ∃ u x : BinaryAdelicGL,
    h = u * x ∧ x ∈ awayGroupA v ∧ ∀ y ∈ awayGroupA v, u * y = y * u := by
  set r := GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) h
  set f := GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) h
  set fv := placePart (v := v) f
  refine ⟨atInfinity r * atFinite fv, atFinite (fv⁻¹ * f), ?_,
    ⟨_, mul_placePart_inv_mem f, rfl⟩, ?_⟩
  · rw [mul_assoc, HeckeTranslate.HeckeInvariance.atFinite_mul, mul_inv_cancel_left]
    exact binary_real_finite h
  · rintro _ ⟨z, hz, rfl⟩
    change atInfinity r * atFinite fv * atFinite z = atFinite z * (atInfinity r * atFinite fv)
    have hc : fv * z = z * fv := placeAt_commute_away _ hz
    rw [mul_assoc, HeckeTranslate.HeckeInvariance.atFinite_mul, hc,
      ← HeckeTranslate.HeckeInvariance.atFinite_mul, ← mul_assoc, ← mul_assoc]
    congr 1
    exact (HeckeTranslate.HeckeInvariance.atFinite_comm_atInfinity _ r).symm

/-- **Hecke operators away from `v` act by scalars** on the vectors of any
`CuspidalRepresentation` fixed by `GL₂(Ẑ^{v}) ⊔ K'`, for every `K'` commuting with
`GL₂(𝔸_f^{v})`. -/
theorem awayHecke_scalar (σ : CuspidalRepresentation) (K' : Subgroup BinaryAdelicGL)
    (hK' : ∀ k ∈ K', ∀ x ∈ awayGroupA v, k * x = x * k)
    {x : BinaryFiniteGL} (hx : x ∈ awayGroup v) :
    ∃ z : ℂ, ∀ vec ∈ fixedVectors σ (awayLevelA v ⊔ K'),
      heckeOperator σ (awayDoubleCoset hx) vec = z • vec := by
  apply localHecke_scalar (awayLevelA v) K' (awayGroupA v)
    (Subgroup.map_mono (awayLevel_le_awayGroup v)) hK' away_decomp (awayGelfand v) le_rfl
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨awayDoubleCoset hy, rfl⟩
  · exact ⟨x, hx, rfl⟩

/-- **The compressed Hecke algebra away from `v` acts by scalars**: every finite combination of
compressions of elements of `GL₂(𝔸_f^{v})` is a scalar on `σ.H^(GL₂(Ẑ^{v}) ⊔ K')`. -/
theorem awayCombination_scalar (σ : CuspidalRepresentation) (K' : Subgroup BinaryAdelicGL)
    (hK' : ∀ k ∈ K', ∀ x ∈ awayGroupA v, k * x = x * k)
    {ι : Type*} (S : Finset ι) (c : ι → ℂ) (x : ι → BinaryFiniteGL)
    (hx : ∀ i ∈ S, x i ∈ awayGroup v) :
    ∃ z : ℂ, ∀ w, (∑ i ∈ S, c i • compression σ (awayLevelA v ⊔ K') (atFinite (x i))) w = z • w :=
  localCombination_scalar (awayLevelA v) K' (awayGroupA v)
    (Subgroup.map_mono (awayLevel_le_awayGroup v)) hK' away_decomp (awayGelfand v) le_rfl
    (by rintro _ ⟨y, hy, rfl⟩; exact ⟨awayDoubleCoset hy, rfl⟩) S c _
    (fun i hi => ⟨x i, hx i hi, rfl⟩)

end TernaryPeriodPolynomials.RepresentationTheory
