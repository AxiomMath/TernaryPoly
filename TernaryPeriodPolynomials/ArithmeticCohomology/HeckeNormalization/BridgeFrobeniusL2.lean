module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeFrobeniusTranspose
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeFrobeniusData
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.BinaryHecke

@[expose] public section


/-!
# L2: transposition of the dual lift

Formalized by Claude Sonnet 5.5.  Discharges `BridgeInterface.L2 p`.

* `finiteIndex_f_range p`: the image of `f = (binDatum p).f` (the matrices with `p ∣ k₁₀`) has finite index in `GL₂(ℤ)`; it contains the
  kernel of reduction mod `p`, using `cjInvUnit` (conjugation by `diag(p, 1)`), the inverse of `cjUnit`.  `exists_finite_orbit_reps`: hence
  `Tri` and `OTE` have finitely many `f(S)`-orbits.
* `pairX_swap`, `pairX_antiLin`: the swap of oriented edges and the antisymmetrizer are self-adjoint for `pairX`.
  `pairX_d1`: `⟨t, d1 x⟩ = ⟨β t, x⟩` for `t ∈ ℚ[Tri]`, `x ∈ P1` (`β = bdryMap`), i.e. `β = d1†`.
* `L2_holds p : BridgeInterface.L2 p`: for a `DualLift` `s`, `lam0` is the transpose of `s.s0` (`exists_transpose` on `Tri`) and
  `lam1 = retr ∘ transpose(incl ∘ s.s1 ∘ retr) ∘ incl` on `P1`; they are `f`-twisted `S`-equivariant, adjoint to `s` for the standard
  pairings, and `d1 ∘ lam1 = lam0 ∘ d1` follows from `β s0 = s1 β` by pairing with `[t]`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

open CategoryTheory Representation Rep TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.BinaryDuality
open TernaryPeriodPolynomials.Argument.HeckeDuality TernaryPeriodPolynomials.Argument.HeckeHomology
open scoped Classical MonoidAlgebra

section Index

variable (p : ℕ) [Fact p.Prime]

/-- Conjugation of an integer `2 × 2` matrix by the permutation matrix `(0 1; 1 0)`. -/
def swapConj (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![M 1 1, M 1 0; M 0 1, M 0 0]

theorem swapConj_mul (M N : Matrix (Fin 2) (Fin 2) ℤ) : swapConj (M * N) = swapConj M * swapConj N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapConj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem swapConj_one : swapConj (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapConj]

theorem swapConj_swapConj (M : Matrix (Fin 2) (Fin 2) ℤ) : swapConj (swapConj M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapConj]

/-- The inverse of `cjMat`: conjugation by `diag(p, 1)`, `(a b; c d) ↦ (a pb; c/p d)`, on matrices with `p ∣ c`. -/
def cjInvMat (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ := swapConj (cjMat p (swapConj M))

theorem cjInvMat_mul {M N : Matrix (Fin 2) (Fin 2) ℤ} (hM : (p : ℤ) ∣ M 1 0) (hN : (p : ℤ) ∣ N 1 0) :
    cjInvMat p (M * N) = cjInvMat p M * cjInvMat p N := by
  unfold cjInvMat
  rw [swapConj_mul, cjMat_mul p (by simpa [swapConj] using hM) (by simpa [swapConj] using hN), swapConj_mul]

theorem cjInvMat_one : cjInvMat p 1 = 1 := by
  unfold cjInvMat
  rw [swapConj_one, cjMat_one, swapConj_one]

theorem dvd_inv_one_zero {K L : Matrix (Fin 2) (Fin 2) ℤ} (hKL : K * L = 1) (h : (p : ℤ) ∣ K 1 0) :
    (p : ℤ) ∣ L 1 0 := by
  have h1 : swapConj K * swapConj L = 1 := by rw [← swapConj_mul, hKL, swapConj_one]
  simpa [swapConj] using dvd_inv_zero_one p h1 (by simpa [swapConj] using h)

/-- Conjugation by `diag(p, 1)` on `GL₂(ℤ)` elements with `p ∣ k₁₀`. -/
def cjInvUnit (k : IntegralGL) (hk : (p : ℤ) ∣ k.val 1 0) : IntegralGL where
  val := cjInvMat p k.val
  inv := cjInvMat p k.inv
  val_inv := by
    rw [← cjInvMat_mul p hk (dvd_inv_one_zero p k.val_inv hk), k.val_inv, cjInvMat_one]
  inv_val := by
    rw [← cjInvMat_mul p (dvd_inv_one_zero p k.val_inv hk) hk, k.inv_val, cjInvMat_one]

omit [Fact p.Prime] in
theorem cjInvMat_zero_one (M : Matrix (Fin 2) (Fin 2) ℤ) : cjInvMat p M 0 1 = p * M 0 1 := by
  simp [cjInvMat, swapConj, cjMat]

theorem cjMat_cjInvMat {M : Matrix (Fin 2) (Fin 2) ℤ} (h : (p : ℤ) ∣ M 1 0) : cjMat p (cjInvMat p M) = M := by
  have hp := p_ne_zero_int (p := p)
  obtain ⟨b, hb⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cjMat, cjInvMat, swapConj, hb, Int.mul_ediv_cancel_left _ hp]

theorem exists_f_preimage (γ : IntegralGL) (hγ : (p : ℤ) ∣ γ.val 1 0) :
    ∃ s : (binDatum p).S, (binDatum p).f s = γ := by
  have hk : (p : ℤ) ∣ (cjInvUnit p γ hγ).val 0 1 := by
    change (p : ℤ) ∣ cjInvMat p γ.val 0 1
    rw [cjInvMat_zero_one]
    exact dvd_mul_right _ _
  refine ⟨⟨cjInvUnit p γ hγ, (mem_commSubgroup_C1 p _).mpr hk⟩, ?_⟩
  apply Units.ext
  rw [binDatum_f_val]
  exact cjMat_cjInvMat p hγ

/-- The image of `f` has finite index: it contains the kernel of reduction mod `p`. -/
theorem finiteIndex_f_range : ((binDatum p).f.range).FiniteIndex := by
  let red : IntegralGL →* GL (Fin 2) (ZMod p) :=
    Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod p))
  have : Finite (GL (Fin 2) (ZMod p)) := inferInstance
  have : red.ker.FiniteIndex := Subgroup.finiteIndex_ker red
  refine Subgroup.finiteIndex_of_le (H := red.ker) ?_
  intro k hk
  have h10 := congrArg (fun m : GL (Fin 2) (ZMod p) => (m : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0)
    (MonoidHom.mem_ker.mp hk)
  simp [red, Matrix.GeneralLinearGroup.map] at h10
  obtain ⟨s, hs⟩ := exists_f_preimage p k ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10)
  exact ⟨s, hs⟩

end Index

section Orbits

variable {Γ : Type} [Group Γ] {X : Type} [MulAction Γ X] {S : Subgroup Γ} (f : S →* Γ)

/-- If `f(S)` has finite index in `Γ` and `Γ` is transitive on `X`, then `X` has finitely many `f(S)`-orbits. -/
theorem exists_finite_orbit_reps [f.range.FiniteIndex] {x₀ : X} (htr : ∀ y : X, ∃ γ : Γ, γ • x₀ = y) :
    ∃ I : Set X, I.Finite ∧ ∀ x, ∃ i ∈ I, ∃ σ : S, x = f σ • i := by
  have : Finite (Γ ⧸ f.range) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨Set.range (fun q : Γ ⧸ f.range => (q.out)⁻¹ • x₀), Set.finite_range _, fun x => ?_⟩
  obtain ⟨γ, rfl⟩ := htr x
  set q : Γ ⧸ f.range := QuotientGroup.mk γ⁻¹ with hq
  have h1 : QuotientGroup.mk q.out = q := QuotientGroup.out_eq' q
  have h2 : (q.out)⁻¹ * γ⁻¹ ∈ f.range := by
    rw [← QuotientGroup.eq]
    rw [h1]
  obtain ⟨σ, hσ⟩ := h2
  refine ⟨(q.out)⁻¹ • x₀, ⟨q, rfl⟩, σ⁻¹, ?_⟩
  rw [map_inv, hσ, ← mul_smul]
  congr 1
  group

end Orbits

section Farey

open BridgeInterface

theorem pairX_neg_left {X : Type} (u v : MonoidAlgebra ℚ X) : pairX (-u) v = -pairX u v := by
  have := pairX_smul_left (-1 : ℚ) u v
  simpa using this

theorem pairX_sub_left {X : Type} (u u' v : MonoidAlgebra ℚ X) : pairX (u - u') v = pairX u v - pairX u' v := by
  rw [sub_eq_add_neg, pairX_add_left, pairX_neg_left, ← sub_eq_add_neg]

theorem pairX_sub_right {X : Type} (u v v' : MonoidAlgebra ℚ X) : pairX u (v - v') = pairX u v - pairX u v' := by
  rw [pairX_comm, pairX_sub_left, pairX_comm v, pairX_comm v']

theorem coeff_swap (c : PE) (q : OTE) : (swapMap.hom c).coeff q = c.coeff q.swap := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb, MonoidAlgebra.coeff_add,
      Finsupp.add_apply]
  | single e r =>
    rw [swapMap_single, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single, Finsupp.single_apply,
      Finsupp.single_apply]
    by_cases h : e = q.swap
    · subst h; simp
    · have : e.swap ≠ q := fun h' => h (by rw [← h', OTE.swap_swap])
      simp [h, this]

theorem pairX_swap (a b : PE) : pairX (swapMap.hom a) b = pairX a (swapMap.hom b) := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, pairX_zero_right, pairX_zero_right]
  | add x y hx hy => rw [map_add, pairX_add_right, pairX_add_right, hx, hy]
  | single e r =>
    rw [pairX_single_right, swapMap_single, pairX_single_right, coeff_swap]

theorem pairX_antiLin (a b : PE) : pairX (antiLin a) b = pairX a (antiLin b) := by
  rw [antiLin_apply, antiLin_apply, pairX_smul_left, pairX_smul_right, pairX_sub_left, pairX_sub_right, pairX_swap]

theorem pairX_sum_left {X ι : Type} (A : Finset ι) (g : ι → MonoidAlgebra ℚ X) (v : MonoidAlgebra ℚ X) :
    pairX (∑ i ∈ A, g i) v = ∑ i ∈ A, pairX (g i) v := by
  induction A using Finset.induction_on with
  | empty => simp [pairX_zero_left]
  | insert a A ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairX_add_left, ih]

theorem coeff_dTilde (c : PE) (t : Tri) :
    (dTilde.hom c).coeff t = ∑ q ∈ inE t, c.coeff q - ∑ q ∈ nbF t, c.coeff q := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, Finset.sum_add_distrib]
    abel
  | single e r =>
    rw [dTilde_single, MonoidAlgebra.coeff_sub, Finsupp.sub_apply]
    simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
    have h1 : e ∈ inE t ↔ e.1.2 = t := mem_inE
    have h2 : e ∈ nbF t ↔ e.1.1 = t := mem_nbF
    by_cases a : e.1.2 = t <;> by_cases b : e.1.1 = t <;> simp [h1, h2, a, b]

theorem pairX_bdryV (t : Tri) (c : PE) :
    pairX (bdryV t) c = ∑ q ∈ nbF t, (c.coeff q.swap - c.coeff q) := by
  unfold bdryV
  rw [pairX_sum_left]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [pairX_sub_left, pairX_single_left, pairX_single_left, one_mul, one_mul]

theorem coeff_swap_of_anti {c : PE} (hc : c ∈ antiSub) (q : OTE) : c.coeff q.swap = -c.coeff q := by
  have h := mem_antiSub.mp hc
  have := congrArg (fun w : PE => w.coeff q) h
  simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply] at this
  rw [coeff_swap] at this
  simp at this
  linarith

theorem coeff_d1_eq (x : P1) (t : Tri) :
    (d1.hom x).coeff t = pairX (bdryV t) (x : PE) := by
  change (dTilde.hom (x : PE)).coeff t = _
  rw [coeff_dTilde, pairX_bdryV]
  have hx := x.2
  have hin : ∑ q ∈ inE t, (x : PE).coeff q = -∑ q ∈ nbF t, (x : PE).coeff q := by
    unfold inE
    rw [Finset.sum_image (fun a _ b _ h => by simpa using congrArg OTE.swap h), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => coeff_swap_of_anti hx a
  have h2 : ∑ q ∈ nbF t, ((x : PE).coeff q.swap - (x : PE).coeff q) =
      ∑ q ∈ nbF t, (-(x : PE).coeff q - (x : PE).coeff q) :=
    Finset.sum_congr rfl fun q _ => by rw [coeff_swap_of_anti hx q]
  rw [hin, h2, Finset.sum_sub_distrib, Finset.sum_neg_distrib]

theorem pairX_d1 (t : P0) (x : P1) : pairX t (d1.hom x) = pairX (bdryMap.hom t) (x : PE) := by
  induction t using MonoidAlgebra.induction_linear with
  | zero => rw [pairX_zero_left, map_zero, pairX_zero_left]
  | add a b ha hb => rw [pairX_add_left, map_add, pairX_add_left, ha, hb]
  | single t r =>
    rw [pairX_single_left, bdryMap_single, pairX_smul_left, coeff_d1_eq]

theorem antiLin_of_mem {c : PE} (hc : c ∈ antiSub) : antiLin c = c := by
  have := LinearMap.congr_fun (congrArg (fun f => f.hom.toLinearMap) inclP1_retrP1) ⟨c, hc⟩
  exact congrArg Subtype.val this

variable (p : ℕ) [Fact p.Prime]

/-- **L2** (`BridgeInterface.L2 p`): every dual lift `s` has a transpose `LiftData`, adjoint to `s` for the standard pairings. -/
theorem L2_holds : BridgeInterface.L2 p := by
  intro s
  have hidx := finiteIndex_f_range p
  have hI0 : ∃ I : Set Tri, I.Finite ∧ ∀ x, ∃ i ∈ I, ∃ σ : (binDatum p).S, x = (binDatum p).f σ • i :=
    exists_finite_orbit_reps (binDatum p).f tri_htr
  have hI1 : ∃ I : Set OTE, I.Finite ∧ ∀ x, ∃ i ∈ I, ∃ σ : (binDatum p).S, x = (binDatum p).f σ • i :=
    exists_finite_orbit_reps (binDatum p).f ote_htr
  obtain ⟨lam0, hadj0, heq0⟩ := exists_transpose (S := (binDatum p).S) (f := (binDatum p).f)
    (s := s.s0) (fun σ w => s.eq0 σ w) hTri hI0
  let s1' : PE →ₗ[ℚ] PE := inclP1.hom.toLinearMap ∘ₗ s.s1 ∘ₗ retrP1.hom.toLinearMap
  have hs1' : ∀ (σ : (binDatum p).S) (w : PE),
      s1' (Representation.ofMulAction ℚ IntegralGL OTE ((binDatum p).f σ) w) =
        Representation.ofMulAction ℚ IntegralGL OTE σ.1 (s1' w) := by
    intro σ w
    change inclP1.hom (s.s1 (retrP1.hom (PE.ρ ((binDatum p).f σ) w))) = PE.ρ σ.1 (inclP1.hom (s.s1 (retrP1.hom w)))
    rw [Rep.hom_comm_apply retrP1, s.eq1, Rep.hom_comm_apply inclP1]
  obtain ⟨l1', hadj1, heq1⟩ := exists_transpose (S := (binDatum p).S) (f := (binDatum p).f)
    (s := s1') hs1' hOTE hI1
  let lam1 : P1 →ₗ[ℚ] P1 := retrP1.hom.toLinearMap ∘ₗ l1' ∘ₗ inclP1.hom.toLinearMap
  have hlam1_coe : ∀ u : P1, ((lam1 u : P1) : PE) = antiLin (l1' (u : PE)) := fun u => rfl
  have hadj1' : ∀ u v : P1, pairX ((lam1 u : P1) : PE) (v : PE) = pairX (u : PE) ((s.s1 v : P1) : PE) := by
    intro u v
    rw [hlam1_coe, pairX_antiLin, antiLin_of_mem v.2, hadj1]
    change pairX (u : PE) (inclP1.hom (s.s1 (retrP1.hom (inclP1.hom v)))) = _
    have : retrP1.hom (inclP1.hom v) = v :=
      LinearMap.congr_fun (congrArg (fun f => f.hom.toLinearMap) inclP1_retrP1) v
    rw [this]
    rfl
  have hD : ∀ (t : P0) (x : P1), pairX t (d1.hom x) = pairX ((betaL t : P1) : PE) (x : PE) := fun t x => pairX_d1 t x
  refine ⟨⟨lam0, lam1, fun σ x => heq0 σ x, fun σ x => ?_, fun x => ?_⟩, hadj0, hadj1'⟩
  · change retrP1.hom (l1' (inclP1.hom (P1.ρ σ.1 x))) = P1.ρ ((binDatum p).f σ) (retrP1.hom (l1' (inclP1.hom x)))
    rw [Rep.hom_comm_apply inclP1, heq1, Rep.hom_comm_apply retrP1]
  · apply eq_of_pairX
    intro t
    have hbs : ((betaL (MonoidAlgebra.single t (1 : ℚ)) : P1) : PE) = bdryMap.hom (MonoidAlgebra.single t (1 : ℚ)) := rfl
    change pairX (d1.hom (lam1 x)) _ = pairX (lam0 (d1.hom x)) _
    rw [pairX_comm, hD, pairX_comm, hadj1', ← s.chain, pairX_comm (x : PE), ← hD, pairX_comm, hadj0]

end Farey

end TernaryPeriodPolynomials.Argument.HeckeNormalization
