module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.ReductionProof
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Local.Iwasawa
public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Levi
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.FiniteSphericalPlane

@[expose] public section


/-!
# The rational Iwasawa decomposition `GL₃(𝔸_f) = P(ℚ) · GL₃(Ẑ)` of the plane parabolic

Formalized by Claude Sonnet 5.5.

* `denom_integral_at`, `local_additive`, `exists_rational_approx`: `𝔸_f = ℚ + Ẑ` (strong approximation for the additive group), by a place-by-place induction (the pattern of H4's `latticeReductionExists`).
* `UA`, `UA_pzpow`, `local_unit`, `exists_rational_unit`: class number one of `ℚ`, `𝔸_f^× = ℚ^× Ẑ^×`.
* `plane_reduce_eq`: the matrix identity reducing a plane-parabolic element by a rational radical-times-Levi element.
* `integral_elt_of_components`, `integral_unit_of_components`, `map_planeUnipotent'`, `map_planeLevi'`: assembly lemmas.
* **`plane_rational_decomp`**: every `p ∈ P(𝔸_f)` is `π k` with `π ∈ P(ℚ)`, `k ∈ GL₃(Ẑ)` (uses H4's `latticeReductionExists` for the Levi block).
* **`finiteGL_eq_planeRational_mul_integral`**: every `g ∈ GL₃(𝔸_f)` is `π k` (with the finite plane Iwasawa decomposition `finitePlane_factorization`).
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalIwasawa
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Argument.LatticeCounts.FiniteReduction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

open scoped Classical

/-- A rational number with only `p_v`-power denominators is integral at every other place. -/
theorem denom_integral_at (v w : FinitePlace) (hwv : w ≠ v) (r : ℚ)
    (hr : ∃ (n : ℤ) (k : ℕ), r * ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) ^ k = n) :
    algebraMap ℚ (w.adicCompletion ℚ) r ∈ OS w := by
  obtain ⟨n, k, h⟩ := hr
  set P : ℚ := ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) with hP
  have hP1 : w.valuation ℚ P = 1 := by
    have h := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (v := w) (K := ℚ)
      (r := ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ))).2 (natGen_notMem v w hwv)
    simpa [hP] using h
  have h1 : w.valuation ℚ (r * P ^ k) ≤ 1 := by
    rw [h]
    have := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (R := ℤ) (v := w) (K := ℚ) n
    simpa using this
  rw [map_mul, map_pow, hP1, one_pow, mul_one] at h1
  have key : Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := ℤ) (v := w) (K := ℚ) r
  show algebraMap ℚ (w.adicCompletion ℚ) r ∈ w.adicCompletionIntegers ℚ
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, key]
  exact h1

/-- **Local additive approximation**: every element of `K_v` is a rational with `p_v`-power denominator modulo `O_v`. -/
theorem local_additive (v : FinitePlace) (x : v.adicCompletion ℚ) :
    ∃ r : ℚ, (∃ (n : ℤ) (k : ℕ), r * ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) ^ k = n) ∧
      x - algebraMap ℚ (v.adicCompletion ℚ) r ∈ OS v := by
  set p : ℕ := (Rat.HeightOneSpectrum.primesEquiv v : ℕ) with hp
  have : Fact p.Prime := inferInstance
  obtain ⟨n, k, hnk⟩ := exists_approx (p := p) (pe v x) (ε := 1) one_pos
  have hp0 : ((p : ℚ)) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  refine ⟨(n : ℚ) / (p : ℚ) ^ k, ⟨n, k, by field_simp⟩, ?_⟩
  rw [mem_iff_norm, map_sub, pe_algebraMap]
  have : algebraMap ℚ ℚ_[p] ((n : ℚ) / (p : ℚ) ^ k) = (n : ℚ_[p]) / (p : ℚ_[p]) ^ k := by
    simp
  rw [this, norm_sub_rev]
  exact hnk.le


/-- **Global additive approximation** (`𝔸_f = ℚ + Ẑ`). -/
theorem exists_rational_approx (x : FiniteAdeles) :
    ∃ r : ℚ, ∀ v : FinitePlace, finiteEvaluation v x - algebraMap ℚ (v.adicCompletion ℚ) r ∈ OS v := by
  have hall : ∀ᶠ v in Filter.cofinite, finiteEvaluation v x ∈ OS v := x.2
  have hT : {v : FinitePlace | ¬ finiteEvaluation v x ∈ OS v}.Finite := Filter.eventually_cofinite.1 hall
  have claim : ∀ S : Finset FinitePlace, ∃ r : ℚ, (∀ w, w ∉ S → algebraMap ℚ (w.adicCompletion ℚ) r ∈ OS w) ∧
      (∀ v ∈ S, finiteEvaluation v x - algebraMap ℚ (v.adicCompletion ℚ) r ∈ OS v) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨0, fun w _ => ?_, fun v hv => by simp at hv⟩
      simp
    | @insert v0 S hv0 ih =>
      obtain ⟨r, hr1, hr2⟩ := ih
      obtain ⟨rl, hrl1, hrl2⟩ := local_additive v0 (finiteEvaluation v0 x - algebraMap ℚ (v0.adicCompletion ℚ) r)
      refine ⟨r + rl, fun w hw => ?_, fun v hv => ?_⟩
      · have hwv : w ≠ v0 := fun h => hw (h ▸ Finset.mem_insert_self _ _)
        have hwS : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
        rw [map_add]
        exact (OS w).add_mem (hr1 w hwS) (denom_integral_at v0 w hwv rl hrl1)
      · rcases Finset.mem_insert.1 hv with h | hvS
        · subst h
          have : finiteEvaluation v (x) - algebraMap ℚ (v.adicCompletion ℚ) (r + rl) =
              (finiteEvaluation v x - algebraMap ℚ (v.adicCompletion ℚ) r) - algebraMap ℚ (v.adicCompletion ℚ) rl := by
            rw [map_add]; ring
          rw [this]; exact hrl2
        · have hvv0 : v ≠ v0 := fun h => hv0 (h ▸ hvS)
          have : finiteEvaluation v x - algebraMap ℚ (v.adicCompletion ℚ) (r + rl) =
              (finiteEvaluation v x - algebraMap ℚ (v.adicCompletion ℚ) r) - algebraMap ℚ (v.adicCompletion ℚ) rl := by
            rw [map_add]; ring
          rw [this]
          exact (OS v).sub_mem (hr2 v hvS) (denom_integral_at v0 v hvv0 rl hrl1)
  obtain ⟨r, hr1, hr2⟩ := claim hT.toFinset
  refine ⟨r, fun v => ?_⟩
  by_cases hv : v ∈ hT.toFinset
  · exact hr2 v hv
  · have hG : finiteEvaluation v x ∈ OS v := by
      by_contra h
      exact hv ((Set.Finite.mem_toFinset hT).2 h)
    exact (OS v).sub_mem hG (hr1 v hv)


/-- Unit of the local ring of integers. -/
def UA (w : FinitePlace) (a : w.adicCompletion ℚ) : Prop := a ∈ OS w ∧ a⁻¹ ∈ OS w

theorem UA.mul {w : FinitePlace} {a b : w.adicCompletion ℚ} (ha : UA w a) (hb : UA w b) : UA w (a * b) :=
  ⟨(OS w).mul_mem ha.1 hb.1, by rw [mul_inv]; exact (OS w).mul_mem ha.2 hb.2⟩

/-- `p_v^e` is a unit at every other place. -/
theorem UA_pzpow (v w : FinitePlace) (hwv : w ≠ v) (e : ℤ) :
    UA w (algebraMap ℚ (w.adicCompletion ℚ) (((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) ^ e)) := by
  set P : ℚ := ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) with hP
  have hP1 : w.valuation ℚ P = 1 := by
    have h := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (v := w) (K := ℚ)
      (r := ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ))).2 (natGen_notMem v w hwv)
    simpa [hP] using h
  have key : ∀ r : ℚ, Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := fun r =>
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := ℤ) (v := w) (K := ℚ) r
  have hmem : ∀ r : ℚ, w.valuation ℚ r ≤ 1 → algebraMap ℚ (w.adicCompletion ℚ) r ∈ OS w := fun r hr => by
    show algebraMap ℚ (w.adicCompletion ℚ) r ∈ w.adicCompletionIntegers ℚ
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, key]
    exact hr
  refine ⟨hmem _ (by rw [map_zpow₀, hP1, one_zpow]), ?_⟩
  rw [← map_inv₀]
  exact hmem _ (by rw [map_inv₀, map_zpow₀, hP1, one_zpow, inv_one])

/-- **Local unit normalisation**: every nonzero element of `K_v` becomes a unit of `O_v` after multiplication by `p_v^e`. -/
theorem local_unit (v : FinitePlace) (x : v.adicCompletion ℚ) (hx : x ≠ 0) :
    ∃ e : ℤ, UA v (algebraMap ℚ (v.adicCompletion ℚ) (((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℚ) ^ e) * x) := by
  set p : ℕ := (Rat.HeightOneSpectrum.primesEquiv v : ℕ) with hp
  have : Fact p.Prime := inferInstance
  have hy : pe v x ≠ 0 := (map_ne_zero (pe v)).2 hx
  refine ⟨-(pe v x).valuation, ?_⟩
  have hnorm : ‖algebraMap ℚ ℚ_[p] ((p : ℚ) ^ (-(pe v x).valuation)) * pe v x‖ = 1 := by
    have h1 : algebraMap ℚ ℚ_[p] ((p : ℚ) ^ (-(pe v x).valuation)) = (p : ℚ_[p]) ^ (-(pe v x).valuation) := by simp
    rw [h1, norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hy, neg_neg, ← zpow_add₀]
    · simp
    · exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hmap : pe v (algebraMap ℚ (v.adicCompletion ℚ) ((p : ℚ) ^ (-(pe v x).valuation)) * x) =
      algebraMap ℚ ℚ_[p] ((p : ℚ) ^ (-(pe v x).valuation)) * pe v x := by
    rw [map_mul, pe_algebraMap]
  refine ⟨?_, ?_⟩
  · rw [mem_iff_norm, hmap, hnorm]
  · rw [mem_iff_norm, map_inv₀, hmap, norm_inv, hnorm]; simp


/-- **Class number one for `ℚ`** (`𝔸_f^× = ℚ^× Ẑ^×`): a finite idele becomes a unit of `Ẑ` after multiplication by a nonzero rational. -/
theorem exists_rational_unit (t : FiniteAdeles) (ht : IsUnit t) :
    ∃ q : ℚ, q ≠ 0 ∧ ∀ v : FinitePlace, UA v (algebraMap ℚ (v.adicCompletion ℚ) q * finiteEvaluation v t) := by
  obtain ⟨u, rfl⟩ := ht
  have hmul : ∀ v, finiteEvaluation v (u : FiniteAdeles) * finiteEvaluation v ((u⁻¹ : FiniteAdelesˣ) : FiniteAdeles) = 1 :=
    fun v => by rw [← map_mul, Units.mul_inv, map_one]
  have hne : ∀ v, finiteEvaluation v (u : FiniteAdeles) ≠ 0 := fun v h => by
    have := hmul v
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have hinv : ∀ v, finiteEvaluation v ((u⁻¹ : FiniteAdelesˣ) : FiniteAdeles) = (finiteEvaluation v (u : FiniteAdeles))⁻¹ :=
    fun v => eq_inv_of_mul_eq_one_right (hmul v)
  have hall : ∀ᶠ v in Filter.cofinite, finiteEvaluation v (u : FiniteAdeles) ∈ OS v ∧
      finiteEvaluation v ((u⁻¹ : FiniteAdelesˣ) : FiniteAdeles) ∈ OS v :=
    (u : FiniteAdeles).2.and ((u⁻¹ : FiniteAdelesˣ) : FiniteAdeles).2
  have hT : {v : FinitePlace | ¬ (finiteEvaluation v (u : FiniteAdeles) ∈ OS v ∧
      finiteEvaluation v ((u⁻¹ : FiniteAdelesˣ) : FiniteAdeles) ∈ OS v)}.Finite := Filter.eventually_cofinite.1 hall
  have claim : ∀ S : Finset FinitePlace, ∃ q : ℚ, q ≠ 0 ∧ (∀ w, w ∉ S → UA w (algebraMap ℚ (w.adicCompletion ℚ) q)) ∧
      (∀ v ∈ S, UA v (algebraMap ℚ (v.adicCompletion ℚ) q * finiteEvaluation v (u : FiniteAdeles))) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨1, one_ne_zero, fun w _ => ?_, fun v hv => by simp at hv⟩
      simp only [map_one]
      exact ⟨(OS w).one_mem, by rw [inv_one]; exact (OS w).one_mem⟩
    | @insert v0 S hv0 ih =>
      obtain ⟨q, hq0, hq1, hq2⟩ := ih
      have hx : algebraMap ℚ (v0.adicCompletion ℚ) q * finiteEvaluation v0 (u : FiniteAdeles) ≠ 0 :=
        mul_ne_zero ((map_ne_zero _).2 hq0) (hne v0)
      obtain ⟨e, he⟩ := local_unit v0 _ hx
      refine ⟨((Rat.HeightOneSpectrum.primesEquiv v0 : ℕ) : ℚ) ^ e * q,
        mul_ne_zero (zpow_ne_zero _ (Nat.cast_ne_zero.2 (Rat.HeightOneSpectrum.primesEquiv v0).2.ne_zero)) hq0,
        fun w hw => ?_, fun v hv => ?_⟩
      · have hwv : w ≠ v0 := fun h => hw (h ▸ Finset.mem_insert_self _ _)
        have hwS : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
        rw [map_mul]
        exact (UA_pzpow v0 w hwv e).mul (hq1 w hwS)
      · rcases Finset.mem_insert.1 hv with h | hvS
        · subst h
          rw [map_mul, mul_assoc]
          exact he
        · have hvv0 : v ≠ v0 := fun h => hv0 (h ▸ hvS)
          rw [map_mul, mul_assoc]
          exact (UA_pzpow v0 v hvv0 e).mul (hq2 v hvS)
  obtain ⟨q, hq0, hq1, hq2⟩ := claim hT.toFinset
  refine ⟨q, hq0, fun v => ?_⟩
  by_cases hv : v ∈ hT.toFinset
  · exact hq2 v hv
  · have hG : finiteEvaluation v (u : FiniteAdeles) ∈ OS v ∧
        finiteEvaluation v ((u⁻¹ : FiniteAdelesˣ) : FiniteAdeles) ∈ OS v := by
      by_contra h
      exact hv ((Set.Finite.mem_toFinset hT).2 h)
    exact (hq1 v hv).mul ⟨hG.1, by rw [← hinv v]; exact hG.2⟩

/-- The algebraic identity behind the decomposition `P(𝔸_f) = P(ℚ) P(Ẑ)`: a rational Levi-radical element reduces `p` to the product of a radical and a Levi element. -/
theorem plane_reduce_eq {R : Type*} [CommRing R] (p : GL3 R) (hp : p ∈ planeParabolic R)
    (γ κ : GeneralLinearGroup (Fin 2) R) (q u : Rˣ) (r0 r1 y0 y1 : R)
    (hκ : κ.val = γ.val * (planeBlockGL p hp).val) (hu : u.val = q.val * p.val 2 2)
    (hy0 : y0 * u.val = (γ.val 0 0 * p.val 0 2 + γ.val 0 1 * p.val 1 2) - r0 * u.val)
    (hy1 : y1 * u.val = (γ.val 1 0 * p.val 0 2 + γ.val 1 1 * p.val 1 2) - r1 * u.val) :
    planeUnipotent (-r0) (-r1) * planeLevi γ q * p = planeUnipotent y0 y1 * planeLevi κ u := by
  have h20 : p.val 2 0 = 0 := hp.1
  have h21 : p.val 2 1 = 0 := hp.2
  have k00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) hκ
  have k01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1) hκ
  have k10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 0) hκ
  have k11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 1) hκ
  simp only [Matrix.mul_apply, Fin.sum_univ_two, planeBlockGL] at k00 k01 k10 k11
  rw [hu] at hy0 hy1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLevi, planeBlock, planeUnipotent, Matrix.mul_apply, Fin.sum_univ_three, h20, h21, hu] <;>
    first
    | exact k00.symm
    | exact k01.symm
    | exact k10.symm
    | exact k11.symm
    | linear_combination (-1 : R) * hy0
    | linear_combination (-1 : R) * hy1


theorem integral_elt_of_components (a : FiniteAdeles) (h : ∀ v, finiteEvaluation v a ∈ OS v) :
    ∃ y : IntegralAdeles, integralEmbedding y = a :=
  ⟨fun v => ⟨finiteEvaluation v a, h v⟩, RestrictedProduct.ext _ _ fun _ => rfl⟩

theorem integral_unit_of_components (a : FiniteAdeles) (hne : ∀ v, finiteEvaluation v a ≠ 0)
    (h : ∀ v, UA v (finiteEvaluation v a)) : ∃ u : IntegralAdelesˣ, integralEmbedding u.val = a := by
  refine ⟨⟨fun v => ⟨finiteEvaluation v a, (h v).1⟩, fun v => ⟨(finiteEvaluation v a)⁻¹, (h v).2⟩, ?_, ?_⟩, ?_⟩
  · funext v; apply Subtype.ext; exact mul_inv_cancel₀ (hne v)
  · funext v; apply Subtype.ext; exact inv_mul_cancel₀ (hne v)
  · exact RestrictedProduct.ext _ _ fun _ => rfl

theorem map_planeUnipotent' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (s t : R) :
    GeneralLinearGroup.map φ (planeUnipotent s t) = planeUnipotent (φ s) (φ t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeUnipotent]

theorem map_planeLevi' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A : GeneralLinearGroup (Fin 2) R) (d : Rˣ) :
    GeneralLinearGroup.map φ (planeLevi A d) = planeLevi (GeneralLinearGroup.map φ A) (Units.map φ.toMonoidHom d) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeLevi, planeBlock, GeneralLinearGroup.val_map_apply]

theorem planeUnipotent_mem' {R : Type*} [CommRing R] (s t : R) : planeUnipotent s t ∈ planeParabolic R := ⟨rfl, rfl⟩

/-- **`GL₃(𝔸_f) ⊇ P(𝔸_f) = P(ℚ) · P(Ẑ)`**: every element of the finite-adelic plane parabolic is a rational plane-parabolic element times an element of `GL₃(Ẑ)`
(`GL₂` lattice reduction of H4, class number one of `ℚ`, and `𝔸_f = ℚ + Ẑ`). -/
theorem plane_rational_decomp (p : FiniteGL) (hp : p ∈ planeParabolic FiniteAdeles) :
    ∃ π : GL3 ℚ, π ∈ planeParabolic ℚ ∧
      ∃ k : GL3 IntegralAdeles, p = rationalFinite π * GeneralLinearGroup.map integralEmbedding k := by
  obtain ⟨⟨γ, -, hint⟩⟩ := TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeReductionProof.latticeReductionExists (planeBlockGL p hp)
  rw [binaryIntegralFinite, MonoidHom.mem_range] at hint
  obtain ⟨κ, hκ⟩ := hint
  obtain ⟨q, hq0, hqU⟩ := exists_rational_unit (planeCornerUnit p hp).val (planeCornerUnit p hp).isUnit
  set tU := planeCornerUnit p hp with htU
  have hcorner : tU.val = p.val 2 2 := rfl
  have htne : ∀ v, finiteEvaluation v tU.val ≠ 0 := fun v h0 => by
    have := congrArg (finiteEvaluation v) tU.val_inv
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have hnev : ∀ v, finiteEvaluation v (algebraMap ℚ FiniteAdeles q * tU.val) ≠ 0 := fun v => by
    rw [map_mul, finiteEvaluation_rational]
    exact mul_ne_zero ((map_ne_zero _).2 hq0) (htne v)
  obtain ⟨uI, huI⟩ := integral_unit_of_components (algebraMap ℚ FiniteAdeles q * tU.val) hnev (fun v => by
    rw [map_mul, finiteEvaluation_rational]; exact hqU v)
  set γF : GeneralLinearGroup (Fin 2) FiniteAdeles := binaryRationalFinite γ with hγF
  have hγval : ∀ i j, γF.val i j = algebraMap ℚ FiniteAdeles (γ.val i j) := fun i j => rfl
  let aa : Fin 2 → FiniteAdeles := fun i => γF.val i 0 * p.val 0 2 + γF.val i 1 * p.val 1 2
  let zz : Fin 2 → FiniteAdeles := fun i => aa i * integralEmbedding ((uI⁻¹ : IntegralAdelesˣ) : IntegralAdeles)
  have hrr : ∀ i, ∃ r : ℚ, ∀ v, finiteEvaluation v (zz i) - algebraMap ℚ (v.adicCompletion ℚ) r ∈ OS v :=
    fun i => exists_rational_approx (zz i)
  choose rr hrr using hrr
  have hyy : ∀ i, ∃ y : IntegralAdeles, integralEmbedding y = zz i - algebraMap ℚ FiniteAdeles (rr i) := fun i =>
    integral_elt_of_components _ (fun v => by rw [map_sub, finiteEvaluation_rational]; exact hrr i v)
  choose yy hyy using hyy
  let κF : GeneralLinearGroup (Fin 2) FiniteAdeles := GeneralLinearGroup.map integralEmbedding κ
  let uF : FiniteAdelesˣ := Units.map integralEmbedding.toMonoidHom uI
  let qF : FiniteAdelesˣ := Units.map (algebraMap ℚ FiniteAdeles).toMonoidHom (Units.mk0 q hq0)
  have hκ' : κF.val = γF.val * (planeBlockGL p hp).val := congrArg Units.val hκ
  have huF : uF.val = qF.val * p.val 2 2 := by
    change integralEmbedding uI.val = algebraMap ℚ FiniteAdeles q * p.val 2 2
    rw [huI, hcorner]
  have hy : ∀ i, integralEmbedding (yy i) * uF.val = aa i - algebraMap ℚ FiniteAdeles (rr i) * uF.val := by
    intro i
    rw [hyy i]
    have hinv : integralEmbedding ((uI⁻¹ : IntegralAdelesˣ) : IntegralAdeles) * uF.val = 1 := by
      change integralEmbedding ((uI⁻¹ : IntegralAdelesˣ) : IntegralAdeles) * integralEmbedding uI.val = 1
      rw [← map_mul, Units.inv_mul, map_one]
    calc (zz i - algebraMap ℚ FiniteAdeles (rr i)) * uF.val
        = aa i * (integralEmbedding ((uI⁻¹ : IntegralAdelesˣ) : IntegralAdeles) * uF.val) - algebraMap ℚ FiniteAdeles (rr i) * uF.val := by
          change (aa i * integralEmbedding ((uI⁻¹ : IntegralAdelesˣ) : IntegralAdeles) - _) * _ = _
          ring
      _ = _ := by rw [hinv, mul_one]
  have key := plane_reduce_eq p hp γF κF qF uF (algebraMap ℚ FiniteAdeles (rr 0)) (algebraMap ℚ FiniteAdeles (rr 1))
    (integralEmbedding (yy 0)) (integralEmbedding (yy 1)) hκ' huF (hy 0) (hy 1)
  let π' : GL3 ℚ := planeUnipotent (-(rr 0)) (-(rr 1)) * planeLevi γ (Units.mk0 q hq0)
  have hπ'F : rationalFinite π' = planeUnipotent (-(algebraMap ℚ FiniteAdeles (rr 0))) (-(algebraMap ℚ FiniteAdeles (rr 1))) *
      planeLevi γF qF := by
    change GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (planeUnipotent (-(rr 0)) (-(rr 1)) * planeLevi γ (Units.mk0 q hq0)) = _
    rw [map_mul, map_planeUnipotent', map_planeLevi']
    simp only [map_neg]
    rfl
  let k : GL3 IntegralAdeles := planeUnipotent (yy 0) (yy 1) * planeLevi κ uI
  have hkF : GeneralLinearGroup.map integralEmbedding k = planeUnipotent (integralEmbedding (yy 0)) (integralEmbedding (yy 1)) *
      planeLevi κF uF := by
    change GeneralLinearGroup.map integralEmbedding (planeUnipotent (yy 0) (yy 1) * planeLevi κ uI) = _
    rw [map_mul, map_planeUnipotent', map_planeLevi']
  refine ⟨π'⁻¹, (planeParabolic ℚ).inv_mem ((planeParabolic ℚ).mul_mem (planeUnipotent_mem' _ _) (planeLevi_mem _ _)), k, ?_⟩
  rw [map_inv, hkF, ← key, ← hπ'F, inv_mul_cancel_left]


/-- **`GL₃(𝔸_f) = P(ℚ) · GL₃(Ẑ)`** (plane parabolic): the rational Iwasawa decomposition needed to define an induced section from classical seeds. -/
theorem finiteGL_eq_planeRational_mul_integral (g : FiniteGL) :
    ∃ π : GL3 ℚ, π ∈ planeParabolic ℚ ∧
      ∃ k : GL3 IntegralAdeles, g = rationalFinite π * GeneralLinearGroup.map integralEmbedding k := by
  obtain ⟨p, hp, k₁, hk₁⟩ := finitePlane_factorization g
  obtain ⟨π, hπ, k, hk⟩ := plane_rational_decomp p hp
  refine ⟨π, hπ, k * k₁, ?_⟩
  rw [hk₁, hk, map_mul, mul_assoc]

end TernaryPeriodPolynomials.Argument.FormClassK
