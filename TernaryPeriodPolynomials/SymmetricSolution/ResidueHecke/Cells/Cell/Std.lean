module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Plane
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Nbrs

@[expose] public section


/-!
# Lemma B.1, boundary route: cancellations in `Φ(RG)` and the boundary of the standard cells

* `cancel_pair`: in the `U`-coinvariants the classes of the ordered cells `(w_u, e₀, m)` and `(w_{-u}, e₀, m)` cancel
  (`m` in the plane, `w_u = (1, u)`): the radical element `U(u)` carries one to the other with the first two entries swapped;
* `phi_d_T3`: `d [(e₀, e₁, e₂)] ≡ [(e₁+e₂, e₀, e₁, e₂)] + [(e₁-e₂, e₀, e₁, e₂)]`;
* `phi_d_hexPlus`, `phi_d_hexMinus`: the boundaries of the two hexagons vanish in `Φ(RG_1)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open CategoryTheory Finsupp TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing GeneralEisenstein
  TernaryPeriodPolynomials.Argument.Lemma33.Retract

theorem tupleVec_of_not_ok {n k : ℕ} {ℓ : Fin k → Line} (h : ¬ TupleOK n ℓ) : tupleVec n ℓ = 0 := by
  unfold tupleVec; rw [dite_eq_right h]

theorem TupleOK.smul_iff {n k : ℕ} (ℓ : Fin k → Line) (g : IntegralGL3) :
    TupleOK n (fun i => g • ℓ i) ↔ TupleOK n ℓ := by
  constructor
  · intro h
    have := h.smul g⁻¹
    simpa [inv_smul_smul] using this
  · intro h; exact h.smul g

theorem TupleOK.perm_iff {n k : ℕ} (ℓ : Fin k → Line) (π : Equiv.Perm (Fin k)) :
    TupleOK n (fun i => ℓ (π i)) ↔ TupleOK n ℓ := by
  constructor
  · intro h
    have := h.perm π.symm
    simpa using this
  · intro h; exact h.perm π

/-- **Cancellation in `Φ`**: the classes of `(w_u, e₀, m)` and `(w_{-u}, e₀, m)` are opposite. -/
theorem cancel_pair (n : ℕ) {k : ℕ} (m : Fin k → Line) (hm : ∀ i, ∃ y, m i = pl y) (u : Fin 2 → ℤ) :
    clsU n (tupleVec n (Fin.cons (wl u) (Fin.cons e0L m : Fin (k + 1) → Line) : Fin (k + 2) → Line)) +
      clsU n (tupleVec n (Fin.cons (wl (-u)) (Fin.cons e0L m : Fin (k + 1) → Line) : Fin (k + 2) → Line)) = 0 := by
  set A : Fin (k + 2) → Line := Fin.cons (wl u) (Fin.cons e0L m : Fin (k + 1) → Line) with hA
  set B : Fin (k + 2) → Line := Fin.cons (wl (-u)) (Fin.cons e0L m : Fin (k + 1) → Line) with hB
  have hfix : ∀ i, radZ u • m i = m i := by
    intro i
    obtain ⟨y, hy⟩ := hm i
    rw [hy, radZ_smul_pl]
  have hs0 : (Equiv.swap (0 : Fin (k + 2)) 1) 0 = 1 := Equiv.swap_apply_left _ _
  have hs1 : (Equiv.swap (0 : Fin (k + 2)) 1) 1 = 0 := Equiv.swap_apply_right _ _
  have hs2 : ∀ l : Fin k, (Equiv.swap (0 : Fin (k + 2)) 1) l.succ.succ = l.succ.succ := by
    intro l
    refine Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) ?_
    intro h
    have h' : (l.succ).succ = (0 : Fin (k + 1)).succ := by rw [Fin.succ_zero_eq_one]; exact h
    exact Fin.succ_ne_zero _ (Fin.succ_injective _ h')
  have hAB : (fun i => radZ u • B i) = fun i => A (Equiv.swap (0 : Fin (k + 2)) 1 i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hs0]
      simp [hA, hB, radZ_smul_wl, e0L_eq]
    · refine Fin.cases ?_ (fun l => ?_) j
      · rw [show (Fin.succ (0 : Fin (k + 1)) : Fin (k + 2)) = 1 from Fin.succ_zero_eq_one, hs1]
        simp [hA, hB, radZ_smul_wl, e0L_eq]
      · rw [hs2 l]
        simp [hA, hB, hfix]
  by_cases hBok : TupleOK n B
  · have hAok : TupleOK n A := by
      have h1 := hBok.smul (radZ u)
      rw [hAB] at h1
      exact (TupleOK.perm_iff A (Equiv.swap 0 1)).mp h1
    have e1 : clsU n (tupleVec n B) = clsU n (tupleVec n (fun i => radZ u • B i)) := by
      rw [← tupleVec_twist hBok (radZ u), clsU_radZ]
    rw [e1, hAB, tupleVec_perm hAok (Equiv.swap 0 1), Equiv.Perm.sign_swap (by simp), clsU_smul]
    simp
  · have hAok : ¬ TupleOK n A := by
      intro hA'
      apply hBok
      have h1 := hA'.perm (Equiv.swap 0 1)
      rw [← hAB] at h1
      exact (TupleOK.smul_iff B (radZ u)).mp h1
    rw [tupleVec_of_not_ok hAok, tupleVec_of_not_ok hBok, clsU_zero, add_zero]

/-- The first standard plane line `(0,1,0)`. -/
def p1 : Line := pl ![1, 0]

/-- The second standard plane line `(0,0,1)`. -/
def p2 : Line := pl ![0, 1]

/-- The standard top cell as an ordered cell. -/
def T3t : Fin 3 → Line := ![e0L, p1, p2]

theorem image_T3t : Finset.univ.image T3t = Cell0Geometry.T0set := by
  ext x
  simp [T3t, e0L, p1, p2, pl, Cell0Geometry.T0set, Cell0Geometry.e0, Cell0Geometry.e1, Cell0Geometry.e2,
    Fin.exists_fin_succ, eq_comm]

theorem planar_T3t : ∀ i : Fin 2, ∃ y, (![p1, p2] : Fin 2 → Line) i = pl y := by
  intro i
  fin_cases i
  · exact ⟨![1, 0], rfl⟩
  · exact ⟨![0, 1], rfl⟩

theorem phi_nbrs_T3t : ∑ w ∈ nbrs Cell0Geometry.T0set,
    clsU 2 (tupleVec 2 (Fin.cons w T3t : Fin 4 → Line)) =
      clsU 2 (tupleVec 2 (Fin.cons (Line.mk ![0, 1, 1]) T3t : Fin 4 → Line)) +
        clsU 2 (tupleVec 2 (Fin.cons (Line.mk ![0, 1, -1]) T3t : Fin 4 → Line)) := by
  rw [nbrs_T0]
  simp [Finset.sum_insert, Line.mk_eq_mk]
  have c1 : clsU 2 (tupleVec 2 (Fin.cons (Line.mk ![1, 1, 0]) T3t : Fin 4 → Line)) +
      clsU 2 (tupleVec 2 (Fin.cons (Line.mk ![1, -1, 0]) T3t : Fin 4 → Line)) = 0 :=
    cancel_pair 2 ![p1, p2] planar_T3t ![1, 0]
  have c2 : clsU 2 (tupleVec 2 (Fin.cons (Line.mk ![1, 0, 1]) T3t : Fin 4 → Line)) +
      clsU 2 (tupleVec 2 (Fin.cons (Line.mk ![1, 0, -1]) T3t : Fin 4 → Line)) = 0 :=
    cancel_pair 2 ![p1, p2] planar_T3t ![0, 1]
  have c3 : clsU 2 (tupleVec 2 (Fin.cons (Line.mk ![1, 1, 1]) T3t : Fin 4 → Line)) +
      clsU 2 (tupleVec 2 (Fin.cons (Line.mk ![1, -1, -1]) T3t : Fin 4 → Line)) = 0 :=
    cancel_pair 2 ![p1, p2] planar_T3t ![1, 1]
  have c4 : clsU 2 (tupleVec 2 (Fin.cons (Line.mk ![1, 1, -1]) T3t : Fin 4 → Line)) +
      clsU 2 (tupleVec 2 (Fin.cons (Line.mk ![1, -1, 1]) T3t : Fin 4 → Line)) = 0 :=
    cancel_pair 2 ![p1, p2] planar_T3t ![1, -1]
  simp only [T3t] at c1 c2 c3 c4 ⊢
  linear_combination (norm := module) c1 + c2 + c3 + c4

theorem tupleOK_T3t : TupleOK 3 T3t := by
  refine ⟨?_, ?_, by norm_num⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [T3t, e0L, p1, p2, pl, Line.mk_eq_mk]
  · rw [image_T3t]
    exact Cell0Geometry.T0.isCell

/-- The first standard hexagon as an ordered cell. -/
def hexP : Fin 4 → Line := ![e0L, p1, p2, pl ![1, 1]]

/-- The second standard hexagon as an ordered cell. -/
def hexM : Fin 4 → Line := ![e0L, p1, p2, pl ![1, -1]]

theorem image_hexP : Finset.univ.image hexP = hexPlusSet := by
  ext x
  simp [hexP, hexPlusSet, e0L, p1, p2, pl, Cell0Geometry.T0set, Cell0Geometry.e0, Cell0Geometry.e1,
    Cell0Geometry.e2, Fin.exists_fin_succ, eq_comm]
  tauto

theorem image_hexM : Finset.univ.image hexM = hexMinusSet := by
  ext x
  simp [hexM, hexMinusSet, e0L, p1, p2, pl, Cell0Geometry.T0set, Cell0Geometry.e0, Cell0Geometry.e1,
    Cell0Geometry.e2, Fin.exists_fin_succ, eq_comm]
  tauto

theorem hexPlusSet_isCell : IsCell hexPlusSet := by
  refine ⟨Cell0Geometry.T0_spans.mono (Finset.subset_insert _ _), ?_⟩
  have hw : Line.mk ![1, 1, 0] ∈ nbrs hexPlusSet := by
    rw [nbrs_hexPlus]; simp
  have := ((mem_nbrs (Cell0Geometry.T0_spans.mono (Finset.subset_insert _ _)) _).mp hw).2
  exact this.mono (Finset.subset_insert _ _)

theorem hexMinusSet_isCell : IsCell hexMinusSet := by
  refine ⟨Cell0Geometry.T0_spans.mono (Finset.subset_insert _ _), ?_⟩
  have hw : Line.mk ![1, 1, 0] ∈ nbrs hexMinusSet := by
    rw [nbrs_hexMinus]; simp
  have := ((mem_nbrs (Cell0Geometry.T0_spans.mono (Finset.subset_insert _ _)) _).mp hw).2
  exact this.mono (Finset.subset_insert _ _)

theorem tupleOK_hexP : TupleOK 2 hexP := by
  refine ⟨?_, ?_, by norm_num⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [hexP, e0L, p1, p2, pl, Line.mk_eq_mk]
  · rw [image_hexP]; exact hexPlusSet_isCell

theorem tupleOK_hexM : TupleOK 2 hexM := by
  refine ⟨?_, ?_, by norm_num⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [hexM, e0L, p1, p2, pl, Line.mk_eq_mk]
  · rw [image_hexM]; exact hexMinusSet_isCell

theorem planar_hexP : ∀ i : Fin 3, ∃ y, (![p1, p2, pl ![1, 1]] : Fin 3 → Line) i = pl y := by
  intro i
  fin_cases i
  · exact ⟨![1, 0], rfl⟩
  · exact ⟨![0, 1], rfl⟩
  · exact ⟨![1, 1], rfl⟩

theorem planar_hexM : ∀ i : Fin 3, ∃ y, (![p1, p2, pl ![1, -1]] : Fin 3 → Line) i = pl y := by
  intro i
  fin_cases i
  · exact ⟨![1, 0], rfl⟩
  · exact ⟨![0, 1], rfl⟩
  · exact ⟨![1, -1], rfl⟩

/-- **The boundary of the first hexagon vanishes in `Φ(RG_1)`.** -/
theorem phi_d_hexP : clsU 1 (dLin 1 (tupleVec 2 hexP)) = 0 := by
  rw [tupleVec_d tupleOK_hexP, image_hexP, nbrs_hexPlus, clsU_sum]
  simp [Finset.sum_insert, Line.mk_eq_mk]
  have c1 : clsU 1 (tupleVec 1 (Fin.cons (Line.mk ![1, 1, 0]) hexP : Fin 5 → Line)) +
      clsU 1 (tupleVec 1 (Fin.cons (Line.mk ![1, -1, 0]) hexP : Fin 5 → Line)) = 0 :=
    cancel_pair 1 ![p1, p2, pl ![1, 1]] planar_hexP ![1, 0]
  have c2 : clsU 1 (tupleVec 1 (Fin.cons (Line.mk ![1, 0, 1]) hexP : Fin 5 → Line)) +
      clsU 1 (tupleVec 1 (Fin.cons (Line.mk ![1, 0, -1]) hexP : Fin 5 → Line)) = 0 :=
    cancel_pair 1 ![p1, p2, pl ![1, 1]] planar_hexP ![0, 1]
  have c3 : clsU 1 (tupleVec 1 (Fin.cons (Line.mk ![1, 1, 1]) hexP : Fin 5 → Line)) +
      clsU 1 (tupleVec 1 (Fin.cons (Line.mk ![1, -1, -1]) hexP : Fin 5 → Line)) = 0 :=
    cancel_pair 1 ![p1, p2, pl ![1, 1]] planar_hexP ![1, 1]
  simp only [hexP] at c1 c2 c3 ⊢
  linear_combination (norm := module) c1 + c2 + c3

/-- **The boundary of the second hexagon vanishes in `Φ(RG_1)`.** -/
theorem phi_d_hexM : clsU 1 (dLin 1 (tupleVec 2 hexM)) = 0 := by
  rw [tupleVec_d tupleOK_hexM, image_hexM, nbrs_hexMinus, clsU_sum]
  simp [Finset.sum_insert, Line.mk_eq_mk]
  have c1 : clsU 1 (tupleVec 1 (Fin.cons (Line.mk ![1, 1, 0]) hexM : Fin 5 → Line)) +
      clsU 1 (tupleVec 1 (Fin.cons (Line.mk ![1, -1, 0]) hexM : Fin 5 → Line)) = 0 :=
    cancel_pair 1 ![p1, p2, pl ![1, -1]] planar_hexM ![1, 0]
  have c2 : clsU 1 (tupleVec 1 (Fin.cons (Line.mk ![1, 0, 1]) hexM : Fin 5 → Line)) +
      clsU 1 (tupleVec 1 (Fin.cons (Line.mk ![1, 0, -1]) hexM : Fin 5 → Line)) = 0 :=
    cancel_pair 1 ![p1, p2, pl ![1, -1]] planar_hexM ![0, 1]
  have c3 : clsU 1 (tupleVec 1 (Fin.cons (Line.mk ![1, 1, -1]) hexM : Fin 5 → Line)) +
      clsU 1 (tupleVec 1 (Fin.cons (Line.mk ![1, -1, 1]) hexM : Fin 5 → Line)) = 0 :=
    cancel_pair 1 ![p1, p2, pl ![1, -1]] planar_hexM ![1, -1]
  simp only [hexM] at c1 c2 c3 ⊢
  linear_combination (norm := module) c1 + c2 + c3

/-- **The boundary of the standard top cell in `Φ(RG_2)`**: the two hexagons. -/
theorem phi_d_T3t : clsU 2 (dLin 2 (tupleVec 3 T3t)) =
    clsU 2 (tupleVec 2 (Fin.cons (pl ![1, 1]) T3t : Fin 4 → Line)) +
      clsU 2 (tupleVec 2 (Fin.cons (pl ![1, -1]) T3t : Fin 4 → Line)) := by
  rw [tupleVec_d tupleOK_T3t, image_T3t, clsU_sum]
  exact phi_nbrs_T3t

end TernaryPeriodPolynomials.Argument.AppendixBResidue
