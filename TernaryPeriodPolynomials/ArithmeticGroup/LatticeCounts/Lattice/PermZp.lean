module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Padic.Surjective
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.HNF
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Lattice.BasisChange

@[expose] public section


/-!
# Lattice permutation over `ℤ_q`, the `ℤ_q`-level core

Formalized by Claude Haiku 5.5.

For a prime `q` and `r`, the Hermite triples `t ∈ hnfData (q^r)` give the lower-triangular integer
matrices `A_t = [[a, 0], [b, d]]` and their `ℤ_q`-reductions `Mz t`. Proved here:

* `range_mulLin_Mz_eq`: the `ℤ_q`-column span of `Mz t` is `latOfZ q r (latOf t)`, the `ℤ_q`-lattice
  attached to `t` by the existing dictionary (`PadicSurjective`, `LatticeHNF`).
* `latPhi`: `t ↦ latOfZ q r (latOf t)` is a bijection from `hnfData (q^r)` onto the index-`q^r`
  `ℤ_q`-lattices of `ℤ_q²` (composite of `hnfEquiv` and `latticeEquivZ`).
* `exists_unit_of_range`: equal column spans give `A = B · C` with `C ∈ GL₂(ℤ_q)`.
* `exists_perm_zp`: for `Y ∈ GL₂(ℤ_q)` there is a permutation `σ` of `hnfData (q^r)` with
  `Y · Mz t = Mz (σ t) · C` for some `C ∈ GL₂(ℤ_q)`. The permutation is induced by `Λ ↦ Y Λ`,
  which preserves the index.
-/

open PadicInt Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermZp

open TernaryPeriodPolynomials.Argument.LatticeCounts
open TernaryPeriodPolynomials.Argument.LatticeCounts.Padic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeBasisChange

variable {q : ℕ} [hq : Fact q.Prime]

/-- Left multiplication by a `2 × 2` matrix over `ℤ_q` on column vectors `(x₁, x₂)ᵀ`. -/
def mulLin (M : Matrix (Fin 2) (Fin 2) ℤ_[q]) : (ℤ_[q] × ℤ_[q]) →ₗ[ℤ_[q]] (ℤ_[q] × ℤ_[q]) where
  toFun x := (M 0 0 * x.1 + M 0 1 * x.2, M 1 0 * x.1 + M 1 1 * x.2)
  map_add' x y := by
    ext <;> simp <;> ring
  map_smul' c x := by
    ext <;> simp <;> ring

theorem mulLin_apply (M : Matrix (Fin 2) (Fin 2) ℤ_[q]) (x : ℤ_[q] × ℤ_[q]) :
    mulLin M x = (M 0 0 * x.1 + M 0 1 * x.2, M 1 0 * x.1 + M 1 1 * x.2) := rfl

theorem mulLin_mul (M N : Matrix (Fin 2) (Fin 2) ℤ_[q]) :
    mulLin (M * N) = (mulLin M).comp (mulLin N) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, mulLin_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ext <;> simp <;> ring

theorem mulLin_one : mulLin (1 : Matrix (Fin 2) (Fin 2) ℤ_[q]) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext <;> simp [mulLin_apply]

theorem mulLin_smul_one (c : ℤ_[q]) (x : ℤ_[q] × ℤ_[q]) :
    mulLin (c • (1 : Matrix (Fin 2) (Fin 2) ℤ_[q])) x = c • x := by
  ext <;> simp [mulLin_apply]

/-- The `ℤ_q`-matrix of a Hermite triple: `[[a, 0], [b, d]]`. -/
def Mz (t : ℕ × ℕ × ℕ) : Matrix (Fin 2) (Fin 2) ℤ_[q] :=
  !![(t.1 : ℤ_[q]), 0; (t.2.1 : ℤ_[q]), (t.2.2 : ℤ_[q])]

theorem Mz_det (t : ℕ × ℕ × ℕ) : (Mz (q := q) t).det = ((t.1 * t.2.2 : ℕ) : ℤ_[q]) := by
  simp [Mz, Matrix.det_fin_two]

/-- `Mz t` applied to `adj (Mz t) y` is `det · y`. -/
theorem mulLin_Mz_adj (t : ℕ × ℕ × ℕ) (y : ℤ_[q] × ℤ_[q]) :
    mulLin (Mz (q := q) t) (mulLin (Mz (q := q) t).adjugate y) = (Mz (q := q) t).det • y := by
  rw [← LinearMap.comp_apply, ← mulLin_mul, Matrix.mul_adjugate, mulLin_smul_one]

/-- The `ℤ_q`-lattice attached to a Hermite triple of level `q^r` is the column span of `Mz t`. -/
theorem range_mulLin_Mz_eq {r : ℕ} (t : ℕ × ℕ × ℕ) (ht : t ∈ hnfData (q ^ r)) :
    LinearMap.range (mulLin (Mz (q := q) t)) = latOfZ q r (latOf t) := by
  have hn : 0 < q ^ r := pow_pos (Fact.out : q.Prime).pos r
  obtain ⟨h1, h2, _⟩ := (mem_hnfData hn t).1 ht
  have hdet : (Mz (q := q) t).det = (q : ℤ_[q]) ^ r := by
    rw [Mz_det, h2]
    push_cast
    rfl
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hA : ((t.1 : ℤ), (t.2.1 : ℤ)) ∈ latOf t := by
      unfold latOf latZ
      exact AddSubgroup.subset_closure (by simp)
    have hD : ((0 : ℤ), (t.2.2 : ℤ)) ∈ latOf t := by
      unfold latOf latZ
      exact AddSubgroup.subset_closure (by simp)
    have hiA : iota q ((t.1 : ℤ), (t.2.1 : ℤ)) ∈ latOfZ q r (latOf t) := by
      show redP (p := q) r (iota q _) ∈ (latOf t).map (redZ q r)
      rw [redP_iota]
      exact AddSubgroup.mem_map_of_mem _ hA
    have hiD : iota q ((0 : ℤ), (t.2.2 : ℤ)) ∈ latOfZ q r (latOf t) := by
      show redP (p := q) r (iota q _) ∈ (latOf t).map (redZ q r)
      rw [redP_iota]
      exact AddSubgroup.mem_map_of_mem _ hD
    have hx : mulLin (Mz (q := q) t) x =
        x.1 • iota q ((t.1 : ℤ), (t.2.1 : ℤ)) + x.2 • iota q ((0 : ℤ), (t.2.2 : ℤ)) := by
      ext <;> simp [mulLin_apply, Mz, iota] <;> ring
    rw [hx]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hiA) (Submodule.smul_mem _ _ hiD)
  · intro x hx
    change redP (p := q) r x ∈ (latOf t).map (redZ q r) at hx
    obtain ⟨ℓ, hℓ, hℓx⟩ := AddSubgroup.mem_map.1 hx
    have hw : redP (p := q) r (x - iota q ℓ) = 0 := by
      rw [map_sub, redP_iota, hℓx, sub_self]
    have hw1 : toZModPow r (x - iota q ℓ).1 = 0 := congrArg Prod.fst hw
    have hw2 : toZModPow r (x - iota q ℓ).2 = 0 := congrArg Prod.snd hw
    have hdv1 : (x - iota q ℓ).1 ∈ Ideal.span {(q : ℤ_[q]) ^ r} := by
      rw [← PadicInt.ker_toZModPow]
      exact hw1
    have hdv2 : (x - iota q ℓ).2 ∈ Ideal.span {(q : ℤ_[q]) ^ r} := by
      rw [← PadicInt.ker_toZModPow]
      exact hw2
    obtain ⟨c1, hc1⟩ := Ideal.mem_span_singleton.1 hdv1
    obtain ⟨c2, hc2⟩ := Ideal.mem_span_singleton.1 hdv2
    have hwmem : x - iota q ℓ ∈ LinearMap.range (mulLin (Mz (q := q) t)) := by
      refine ⟨mulLin (Mz (q := q) t).adjugate (c1, c2), ?_⟩
      rw [mulLin_Mz_adj, hdet]
      refine Prod.ext ?_ ?_
      · simp only [Prod.smul_fst, smul_eq_mul]
        rw [hc1]
      · simp only [Prod.smul_snd, smul_eq_mul]
        rw [hc2]
    have hℓmem : iota q ℓ ∈ LinearMap.range (mulLin (Mz (q := q) t)) := by
      rw [latOf, mem_latZ] at hℓ
      obtain ⟨m, j, hm1, hm2⟩ := hℓ
      refine ⟨(m, j), ?_⟩
      ext <;> simp [mulLin_apply, Mz, iota, hm1, hm2] <;> ring
    have := Submodule.add_mem _ hwmem hℓmem
    simpa using this

/-- The lattice attached to `t`, as an element of the index-`q^r` lattices. -/
noncomputable def latPhi (q r : ℕ) [Fact q.Prime] (hn : 0 < q ^ r) :
    {t // t ∈ hnfData (q ^ r)} ≃
      {Λ : Submodule ℤ_[q] (ℤ_[q] × ℤ_[q]) // Λ.toAddSubgroup.index = q ^ r} :=
  (hnfEquiv hn).trans (latticeEquivZ q r).symm

theorem mulLin_inv_left (Y : Matrix (Fin 2) (Fin 2) ℤ_[q]) (hY : IsUnit Y.det)
    (x : ℤ_[q] × ℤ_[q]) : mulLin Y⁻¹ (mulLin Y x) = x := by
  have h : (mulLin Y⁻¹).comp (mulLin Y) = LinearMap.id := by
    rw [← mulLin_mul, Matrix.nonsing_inv_mul Y hY, mulLin_one]
  exact congrArg (fun f : (ℤ_[q] × ℤ_[q]) →ₗ[ℤ_[q]] (ℤ_[q] × ℤ_[q]) => f x) h

theorem mulLin_inv_right (Y : Matrix (Fin 2) (Fin 2) ℤ_[q]) (hY : IsUnit Y.det)
    (x : ℤ_[q] × ℤ_[q]) : mulLin Y (mulLin Y⁻¹ x) = x := by
  have h : (mulLin Y).comp (mulLin Y⁻¹) = LinearMap.id := by
    rw [← mulLin_mul, Matrix.mul_nonsing_inv Y hY, mulLin_one]
  exact congrArg (fun f : (ℤ_[q] × ℤ_[q]) →ₗ[ℤ_[q]] (ℤ_[q] × ℤ_[q]) => f x) h

/-- The matrix `Y` acting as a linear equivalence on `ℤ_q²`, for `Y ∈ GL₂(ℤ_q)`. -/
def mulEquiv (Y : Matrix (Fin 2) (Fin 2) ℤ_[q]) (hY : IsUnit Y.det) :
    (ℤ_[q] × ℤ_[q]) ≃ₗ[ℤ_[q]] (ℤ_[q] × ℤ_[q]) where
  toLinearMap := mulLin Y
  invFun := mulLin Y⁻¹
  left_inv := fun x => mulLin_inv_left Y hY x
  right_inv := fun x => mulLin_inv_right Y hY x

theorem index_map_mulLin (Y : Matrix (Fin 2) (Fin 2) ℤ_[q]) (hY : IsUnit Y.det)
    (Λ : Submodule ℤ_[q] (ℤ_[q] × ℤ_[q])) :
    (Λ.map (mulLin Y)).toAddSubgroup.index = Λ.toAddSubgroup.index :=
  AddSubgroup.index_map_equiv Λ.toAddSubgroup (mulEquiv Y hY).toAddEquiv

/-- The action of `Y ∈ GL₂(ℤ_q)` on index-`q^r` lattices. -/
noncomputable def actS (r : ℕ) (Y : Matrix (Fin 2) (Fin 2) ℤ_[q]) (hY : IsUnit Y.det) :
    {Λ : Submodule ℤ_[q] (ℤ_[q] × ℤ_[q]) // Λ.toAddSubgroup.index = q ^ r} →
      {Λ : Submodule ℤ_[q] (ℤ_[q] × ℤ_[q]) // Λ.toAddSubgroup.index = q ^ r} :=
  fun Λ => ⟨Λ.1.map (mulLin Y), (index_map_mulLin Y hY Λ.1).trans Λ.2⟩

theorem actS_injective (r : ℕ) (Y : Matrix (Fin 2) (Fin 2) ℤ_[q]) (hY : IsUnit Y.det) :
    Function.Injective (actS r Y hY) := by
  intro a b h
  apply Subtype.ext
  have h' : a.1.map (mulLin Y) = b.1.map (mulLin Y) := congrArg Subtype.val h
  exact Submodule.map_injective_of_injective (mulEquiv Y hY).injective h'

theorem colVec_mem_range (A : Matrix (Fin 2) (Fin 2) ℤ_[q]) (j : Fin 2) :
    ((A 0 j, A 1 j) : ℤ_[q] × ℤ_[q]) ∈ LinearMap.range (mulLin A) := by
  fin_cases j
  · exact ⟨(1, 0), by ext <;> simp [mulLin_apply]⟩
  · exact ⟨(0, 1), by ext <;> simp [mulLin_apply]⟩

theorem coord_of_range (B : Matrix (Fin 2) (Fin 2) ℤ_[q]) (x : ℤ_[q] × ℤ_[q])
    (hx : x ∈ LinearMap.range (mulLin B)) :
    ∃ c : Fin 2 → ℤ_[q], ∀ i : Fin 2, ![x.1, x.2] i = ∑ k, B i k * c k := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨![y.1, y.2], fun i => ?_⟩
  fin_cases i <;> simp [mulLin_apply, Fin.sum_univ_two]

/-- Equal `ℤ_q`-column spans of a matrix with nonzero determinant give `A = B · C`, `C ∈ GL₂(ℤ_q)`. -/
theorem exists_unit_of_range (A B : Matrix (Fin 2) (Fin 2) ℤ_[q]) (hA : A.det ≠ 0)
    (hspan : LinearMap.range (mulLin A) = LinearMap.range (mulLin B)) :
    ∃ C : (Matrix (Fin 2) (Fin 2) ℤ_[q])ˣ, A = B * C.val := by
  have hAq : IsUnit (A.map cq).det := by
    rw [show (A.map cq).det = cq A.det from (RingHom.map_det cq A).symm]
    exact isUnit_iff_ne_zero.2 (fun h => hA (cq_injective (by rw [h, map_zero])))
  have hAB : ∀ j : Fin 2, ∃ c : Fin 2 → ℤ_[q], ∀ i : Fin 2,
      (A.map cq) i j = ∑ k, (B.map cq) i k * (c k : ℚ_[q]) := by
    intro j
    obtain ⟨c, hc⟩ := coord_of_range B (A 0 j, A 1 j) (hspan ▸ colVec_mem_range A j)
    refine ⟨c, fun i => ?_⟩
    have hAi : A i j = ![(A 0 j, A 1 j).1, (A 0 j, A 1 j).2] i := by
      fin_cases i <;> rfl
    have key : A i j = ∑ k, B i k * c k := hAi.trans (hc i)
    show cq (A i j) = ∑ k, cq (B i k) * cq (c k)
    rw [key, map_sum]
    simp [map_mul]
  have hBA : ∀ j : Fin 2, ∃ d : Fin 2 → ℤ_[q], ∀ i : Fin 2,
      (B.map cq) i j = ∑ k, (A.map cq) i k * (d k : ℚ_[q]) := by
    intro j
    obtain ⟨d, hd⟩ := coord_of_range A (B 0 j, B 1 j) (hspan.symm ▸ colVec_mem_range B j)
    refine ⟨d, fun i => ?_⟩
    have hBi : B i j = ![(B 0 j, B 1 j).1, (B 0 j, B 1 j).2] i := by
      fin_cases i <;> rfl
    have key : B i j = ∑ k, A i k * d k := hBi.trans (hd i)
    show cq (B i j) = ∑ k, cq (A i k) * cq (d k)
    rw [key, map_sum]
    simp [map_mul]
  obtain ⟨C, hC⟩ := exists_gl_of_span (A.map cq) (B.map cq) hAq hAB hBA
  refine ⟨C, ?_⟩
  apply Matrix.map_injective cq_injective
  show A.map cq = (B * C.val).map cq
  rw [Matrix.map_mul]
  exact hC

/-- **Permutation of Hermite lattices over `ℤ_q`.** For `Y ∈ GL₂(ℤ_q)` there is a permutation `σ`
of the Hermite triples of level `q^r` with `Y · Mz t = Mz (σ t) · C`, `C ∈ GL₂(ℤ_q)`. -/
theorem exists_perm_zp (r : ℕ) (hn : 0 < q ^ r) (Y : Matrix (Fin 2) (Fin 2) ℤ_[q])
    (hY : IsUnit Y.det) :
    ∃ σ : {t // t ∈ hnfData (q ^ r)} ≃ {t // t ∈ hnfData (q ^ r)},
      ∀ t : {t // t ∈ hnfData (q ^ r)}, ∃ C : (Matrix (Fin 2) (Fin 2) ℤ_[q])ˣ,
        Y * Mz t.1 = Mz (σ t).1 * C.val := by
  let Φ := latPhi q r hn
  let g := actS (q := q) r Y hY
  let G : {t // t ∈ hnfData (q ^ r)} → {t // t ∈ hnfData (q ^ r)} :=
    fun t => Φ.symm (g (Φ t))
  have hGinj : Function.Injective G := by
    intro a b hab
    have h1 : g (Φ a) = g (Φ b) := by
      have := congrArg Φ hab
      simpa [G] using this
    exact Φ.injective (actS_injective r Y hY h1)
  let σ := Equiv.ofBijective G ⟨hGinj, Finite.injective_iff_surjective.mp hGinj⟩
  refine ⟨σ, fun t => ?_⟩
  have hA : (Y * Mz t.1).det ≠ 0 := by
    obtain ⟨_, h2, _⟩ := (mem_hnfData hn t.1).1 t.2
    rw [Matrix.det_mul, Mz_det, h2]
    refine mul_ne_zero hY.ne_zero ?_
    exact Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : q.Prime).ne_zero)
  have hσ : (Φ (σ t)).1 = (g (Φ t)).1 := by
    have : Φ (σ t) = g (Φ t) := Equiv.apply_symm_apply Φ _
    rw [this]
  have hrange : LinearMap.range (mulLin (Y * Mz t.1)) =
      LinearMap.range (mulLin (Mz (σ t).1)) := by
    have hL : LinearMap.range (mulLin (Y * Mz t.1)) = (Φ t).1.map (mulLin Y) := by
      rw [mulLin_mul, LinearMap.range_comp, range_mulLin_Mz_eq t.1 t.2]
      rfl
    have hR : LinearMap.range (mulLin (Mz (σ t).1)) = (Φ (σ t)).1 :=
      range_mulLin_Mz_eq (σ t).1 (σ t).2
    rw [hL, hR, hσ]
    rfl
  exact exists_unit_of_range (Y * Mz t.1) (Mz (σ t).1) hA hrange |>.elim fun C hC => ⟨C, hC⟩

end TernaryPeriodPolynomials.Argument.LatticeCounts.LatticePermZp

end
