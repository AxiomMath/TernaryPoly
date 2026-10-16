module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.RationalKernel
public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Haar

@[expose] public section


/-!
# (C), step 1: the lattice `N Ẑ ⊂ 𝔸_f`, its Haar measure `1/N`, and strong approximation modulo it

Formalized by Claude Sonnet 5.5.

* `latSet N = N Ẑ`, open; `rat_in_lat`: a rational number in `N Ẑ` is `N` times an integer.
* `exists_int_sub_mem_lat`: `Ẑ = ℤ + N Ẑ`; `exists_rat_sub_mem_lat`: `𝔸_f = ℚ + N Ẑ`.
* `finiteMeasure_latSet : μ(N Ẑ) = 1/N` (counting the `N` cosets `j + N Ẑ` of `Ẑ`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

/-- The open lattice `N Ẑ ⊂ 𝔸_f`. -/
def latSet (N : ℕ) : Set FiniteAdeles :=
  (fun x => algebraMap ℚ FiniteAdeles ((N : ℚ)⁻¹) * x) ⁻¹' Set.range integralEmbedding

theorem natCast_eq_algebraMap (N : ℕ) : ((N : ℕ) : FiniteAdeles) = algebraMap ℚ FiniteAdeles (N : ℚ) :=
  (map_natCast (algebraMap ℚ FiniteAdeles) N).symm

theorem invN_mul_N (N : ℕ) [NeZero N] : algebraMap ℚ FiniteAdeles ((N : ℚ)⁻¹) * (N : FiniteAdeles) = 1 := by
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  rw [natCast_eq_algebraMap, ← map_mul, inv_mul_cancel₀ hN, map_one]

variable (N : ℕ) [NeZero N]

theorem mem_latSet_iff (x : FiniteAdeles) :
    x ∈ latSet N ↔ ∃ z : IntegralAdeles, x = (N : FiniteAdeles) * integralEmbedding z := by
  have h1 := invN_mul_N N
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hz' : algebraMap ℚ FiniteAdeles ((N : ℚ)⁻¹) * x = integralEmbedding z := hz.symm
    calc x = (N : FiniteAdeles) * (algebraMap ℚ FiniteAdeles ((N : ℚ)⁻¹) * x) := by
          linear_combination (-x) * h1
      _ = _ := by rw [hz']
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    show integralEmbedding z = algebraMap ℚ FiniteAdeles ((N : ℚ)⁻¹) * ((N : FiniteAdeles) * integralEmbedding z)
    linear_combination (-(integralEmbedding z)) * h1

omit [NeZero N] in
theorem latSet_isOpen : IsOpen (latSet N) :=
  integralLattice_isOpen.preimage (continuous_const.mul continuous_id)

omit [NeZero N] in
theorem latSet_measurable : MeasurableSet (latSet N) := (latSet_isOpen N).measurableSet

/-- A rational number lying in `N Ẑ` is `N` times an integer. -/
theorem rat_in_lat {q : ℚ} (h : algebraMap ℚ FiniteAdeles q ∈ latSet N) : ∃ z : ℤ, q = N * z := by
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have h1 := invN_mul_N N
  obtain ⟨z, hz⟩ := (mem_latSet_iff N _).1 h
  have e : algebraMap ℚ FiniteAdeles (q / N) = integralEmbedding z := by
    rw [div_eq_mul_inv, map_mul, hz]
    linear_combination (integralEmbedding z) * h1
  obtain ⟨j, hj⟩ := rat_mem_int (q / N) (fun v => by
    have h2 : finiteEvaluation v (algebraMap ℚ FiniteAdeles (q / N)) = algebraMap ℚ (v.adicCompletion ℚ) (q / N) :=
      finiteEvaluation_rational v _
    rw [← h2, e]
    exact (z v).2)
  exact ⟨j, by rw [hj]; field_simp⟩

theorem exists_rat_sub_mem_lat (x : FiniteAdeles) :
    ∃ r : ℚ, x - algebraMap ℚ FiniteAdeles r ∈ latSet N := by
  have h1 := invN_mul_N N
  obtain ⟨r0, hr0⟩ := exists_rational_approx (algebraMap ℚ FiniteAdeles ((N : ℚ)⁻¹) * x)
  obtain ⟨w, hw⟩ := integral_elt_of_components
    (algebraMap ℚ FiniteAdeles ((N : ℚ)⁻¹) * x - algebraMap ℚ FiniteAdeles r0) (fun v => by
      rw [map_sub, finiteEvaluation_rational]
      exact hr0 v)
  refine ⟨N * r0, (mem_latSet_iff N _).2 ⟨w, ?_⟩⟩
  rw [map_mul, ← natCast_eq_algebraMap, hw]
  linear_combination (-x) * h1

theorem exists_int_sub_mem_lat (z : IntegralAdeles) :
    ∃ j : ℤ, integralEmbedding z - (j : FiniteAdeles) ∈ latSet N := by
  obtain ⟨r, hr⟩ := exists_rat_sub_mem_lat N (integralEmbedding z)
  obtain ⟨w, hw⟩ := (mem_latSet_iff N _).1 hr
  have hr' : algebraMap ℚ FiniteAdeles r = integralEmbedding (z - N * w) := by
    rw [map_sub, map_mul, map_natCast]
    linear_combination -hw
  obtain ⟨j, hj⟩ := rat_mem_int r (fun v => by
    rw [← finiteEvaluation_rational, hr']
    exact ((z - N * w) v).2)
  refine ⟨j, ?_⟩
  have : (j : FiniteAdeles) = algebraMap ℚ FiniteAdeles r := by rw [← hj]; simp
  rw [this]
  exact hr

theorem latSet_add {x y : FiniteAdeles} (hx : x ∈ latSet N) (hy : y ∈ latSet N) : x + y ∈ latSet N := by
  obtain ⟨z1, rfl⟩ := (mem_latSet_iff N _).1 hx
  obtain ⟨z2, rfl⟩ := (mem_latSet_iff N _).1 hy
  exact (mem_latSet_iff N _).2 ⟨z1 + z2, by rw [map_add]; ring⟩

theorem latSet_neg {x : FiniteAdeles} (hx : x ∈ latSet N) : -x ∈ latSet N := by
  obtain ⟨z1, rfl⟩ := (mem_latSet_iff N _).1 hx
  exact (mem_latSet_iff N _).2 ⟨-z1, by rw [map_neg]; ring⟩

theorem latSet_natCast_mul (q : ℤ) : ((N * q : ℤ) : FiniteAdeles) ∈ latSet N :=
  (mem_latSet_iff N _).2 ⟨(q : IntegralAdeles), by push_cast; simp⟩

theorem latSet_sub {x y : FiniteAdeles} (hx : x ∈ latSet N) (hy : y ∈ latSet N) : x - y ∈ latSet N := by
  rw [sub_eq_add_neg]; exact latSet_add N hx (latSet_neg N hy)

/-- The coset `a + N Ẑ`, as the preimage of `N Ẑ` under `x ↦ x - a`. -/
def latCoset (a : FiniteAdeles) : Set FiniteAdeles := (fun x => x + -a) ⁻¹' latSet N

omit [NeZero N] in
theorem mem_latCoset {a x : FiniteAdeles} : x ∈ latCoset N a ↔ x - a ∈ latSet N := by
  rw [latCoset, Set.mem_preimage, sub_eq_add_neg]

omit [NeZero N] in
theorem latCoset_measurable (a : FiniteAdeles) : MeasurableSet (latCoset N a) :=
  (latSet_measurable N).preimage (measurable_id.add_const _)

omit [NeZero N] in
theorem finiteMeasure_latCoset (a : FiniteAdeles) : finiteMeasure (latCoset N a) = finiteMeasure (latSet N) :=
  measure_preimage_add_right finiteMeasure (-a) (latSet N)

theorem range_integralEmbedding_eq_iUnion :
    Set.range integralEmbedding = ⋃ a : ZMod N, latCoset N (((a.val : ℕ) : FiniteAdeles)) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨j, hj⟩ := exists_int_sub_mem_lat N z
    refine Set.mem_iUnion.2 ⟨(j : ZMod N), (mem_latCoset N).2 ?_⟩
    have hv : (((j : ZMod N).val : ℕ) : ℤ) = j - N * (j / N) := by
      rw [ZMod.val_intCast, Int.emod_def]
    have e : integralEmbedding z - (((j : ZMod N).val : ℕ) : FiniteAdeles) =
        (integralEmbedding z - (j : FiniteAdeles)) + ((N * (j / N) : ℤ) : FiniteAdeles) := by
      have : ((((j : ZMod N).val : ℕ) : ℤ) : FiniteAdeles) = (j : FiniteAdeles) - ((N * (j / N) : ℤ) : FiniteAdeles) := by
        rw [hv]; push_cast; ring
      rw [← Int.cast_natCast, this]; ring
    rw [e]
    exact latSet_add N hj (latSet_natCast_mul N _)
  · intro hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx
    obtain ⟨w, hw⟩ := (mem_latSet_iff N _).1 ((mem_latCoset N).1 ha)
    exact ⟨((a.val : ℕ) : IntegralAdeles) + N * w, by
      rw [map_add, map_mul, map_natCast, map_natCast]
      linear_combination -hw⟩

theorem latCoset_disjoint : Pairwise (Function.onFun Disjoint fun a : ZMod N => latCoset N (((a.val : ℕ) : FiniteAdeles))) := by
  intro a b hab
  rw [Function.onFun, Set.disjoint_left]
  intro x hxa hxb
  have h := latSet_sub N ((mem_latCoset N).1 hxb) ((mem_latCoset N).1 hxa)
  have e : x - ((b.val : ℕ) : FiniteAdeles) - (x - ((a.val : ℕ) : FiniteAdeles)) =
      algebraMap ℚ FiniteAdeles (((a.val : ℤ) - (b.val : ℤ) : ℤ) : ℚ) := by
    push_cast
    ring
  rw [e] at h
  obtain ⟨z, hz⟩ := rat_in_lat N h
  apply hab
  have hz' : (((a.val : ℤ) - (b.val : ℤ) : ℤ)) = N * z := by exact_mod_cast hz
  have : (((a.val : ℤ) - (b.val : ℤ) : ℤ) : ZMod N) = 0 := by
    rw [hz']; push_cast; simp
  rw [Int.cast_sub] at this
  simpa using sub_eq_zero.1 (by simpa using this : ((a.val : ℕ) : ZMod N) - ((b.val : ℕ) : ZMod N) = 0)

/-- **`vol(N Ẑ) = 1/N`** (the `N` cosets `a + N Ẑ`, `a ∈ ℤ/N`, tile `Ẑ`, which has volume `1`). -/
theorem finiteMeasure_latSet : finiteMeasure (latSet N) = (N : ENNReal)⁻¹ := by
  have h1 : finiteMeasure (Set.range integralEmbedding) = 1 := finiteMeasure_integralLattice
  rw [range_integralEmbedding_eq_iUnion N, measure_iUnion (latCoset_disjoint N)
    (fun a => latCoset_measurable N _)] at h1
  simp only [finiteMeasure_latCoset, tsum_fintype, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul] at h1
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm])

end TernaryPeriodPolynomials.Argument.FormClassK
