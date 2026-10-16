module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Orient.Fan

@[expose] public section


/-!
# The cells above the standard top cell, and their linearized barycentres

The standard top cell `T₀ = {e₁, e₂, e₃}` of the well-rounded retract has sixteen vertices
`vtx16 k`; the six minimal lines of the `k`-th vertex are `T₀` together with three of the ten lines
`e_i ± e_j`, `±e₁ ± e₂ ± e₃`.  With the thirteen lines `lineV` and the index sets `Mk k`
(`vtx16_M : (vtx16 k).M = (Mk k).image lineOf`, from `qf_Mk` and cardinality):

* `cell_above`: every cell `D ⊇ T₀` is `D.val = (Ix D).image lineOf` with `Ix D ⊆ Mk k` for some `k`;
* `vertFin_above`: its vertices are the `vtx16 k` with `Ix D ⊆ Mk k`;
* `Lc_bpt`: `Lc (bpt D) = ofQ (bLq (Ix D))`, an explicit rational vector (the linearized barycentre of
  the vertices of `D`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry
  TernaryPeriodPolynomials.FreeResolution

namespace TernaryPeriodPolynomials.Argument.Lemma33.Orient

/-- The thirteen lines occurring in the standard top cell: the coordinate axes and the ten lines
`e_i ± e_j`, `±e₁ ± e₂ ± e₃` through its facets. -/
def lineV : Fin 13 → Vec :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![0, 1, -1], ![0, 1, 1], ![1, -1, -1], ![1, -1, 0],
    ![1, -1, 1], ![1, 0, -1], ![1, 0, 1], ![1, 1, -1], ![1, 1, 0], ![1, 1, 1]]

/-- The indices of the six minimal lines of the `k`-th vertex of the standard top cell. -/
def Mk : Fin 16 → Finset (Fin 13) :=
  ![{0, 1, 2, 9, 11, 12}, {0, 1, 2, 3, 9, 11}, {0, 1, 2, 4, 11, 12}, {0, 1, 2, 3, 10, 11},
    {0, 1, 2, 4, 8, 11}, {0, 1, 2, 8, 10, 11}, {0, 1, 2, 4, 9, 12}, {0, 1, 2, 3, 7, 9},
    {0, 1, 2, 4, 5, 8}, {0, 1, 2, 3, 8, 10}, {0, 1, 2, 4, 6, 9}, {0, 1, 2, 6, 7, 9},
    {0, 1, 2, 4, 5, 6}, {0, 1, 2, 3, 6, 7}, {0, 1, 2, 5, 6, 8}, {0, 1, 2, 3, 6, 8}]

theorem lineV_inj : ∀ i j : Fin 13, (lineV j = lineV i ∨ lineV j = -lineV i) → i = j := by
  decide

theorem lineV_ne_zero : ∀ i : Fin 13, lineV i ≠ 0 := by decide

theorem Mk_card : ∀ k, (Mk k).card = 6 := by decide

theorem Mk_base : ∀ k, ({0, 1, 2} : Finset (Fin 13)) ⊆ Mk k := by decide

theorem qf_Mk : ∀ k : Fin 16, ∀ i ∈ Mk k,
    qf (gram3 (triples k).1 (triples k).2.1 (triples k).2.2) (lineV i) = 1 := by
  decide +kernel


/-! ### Cells above the standard top cell -/

/-- The line with index `i`. -/
def lineOf (i : Fin 13) : Line := Line.mk (lineV i)

theorem lineOf_injective : Function.Injective lineOf := by
  intro i j h
  have := Line.mk_eq_mk.mp h
  exact lineV_inj i j this

theorem T0_val : T0.val = ({0, 1, 2} : Finset (Fin 13)).image lineOf := by
  decide

theorem vtx16_M (k : Fin 16) : (vtx16 k).M = (Mk k).image lineOf := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro ℓ hℓ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hℓ
    exact (Vtx.mem_M_mk (vtx16 k) (lineV i)).mpr (qf_Mk k i hi)
  · rw [Vtx.card_M, Finset.card_image_of_injective _ lineOf_injective, Mk_card]

/-- The indices of the lines of a cell. -/
def Ix (D : Cell) : Finset (Fin 13) := Finset.univ.filter fun i => lineOf i ∈ D.val

theorem mem_Ix (D : Cell) (i : Fin 13) : i ∈ Ix D ↔ lineOf i ∈ D.val := by
  simp [Ix]

theorem cell_above (D : Cell) (h : T0.val ⊆ D.val) :
    D.val = (Ix D).image lineOf ∧ ∃ k, Ix D ⊆ Mk k := by
  obtain ⟨v, hv⟩ := D.isCell.2
  have hvT : v ∈ vertFin T0 := (mem_vertFin T0 v).mpr (h.trans hv)
  rw [vertFin_T0] at hvT
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hvT
  rw [vtx16_M] at hv
  refine ⟨?_, k, ?_⟩
  · ext ℓ
    constructor
    · intro hℓ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hv hℓ)
      exact Finset.mem_image.mpr ⟨i, (mem_Ix D i).mpr hℓ, rfl⟩
    · intro hℓ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hℓ
      exact (mem_Ix D i).mp hi
  · intro i hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp (hv ((mem_Ix D i).mp hi))
    rw [lineOf_injective hji] at hj
    exact hj

theorem Ix_T0 : Ix T0 = {0, 1, 2} := by
  ext i
  rw [mem_Ix, T0_val]
  constructor
  · intro h
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
    rw [← lineOf_injective hji]
    exact hj
  · intro h
    exact Finset.mem_image.mpr ⟨i, h, rfl⟩

theorem vertFin_above (D : Cell) (h : T0.val ⊆ D.val) :
    vertFin D = (Finset.univ.filter fun k : Fin 16 => Ix D ⊆ Mk k).image vtx16 := by
  obtain ⟨hD, -⟩ := cell_above D h
  ext v
  rw [mem_vertFin, Finset.mem_image]
  constructor
  · intro hv
    have hvT : v ∈ vertFin T0 := (mem_vertFin T0 v).mpr (h.trans hv)
    rw [vertFin_T0] at hvT
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hvT
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    intro i hi
    have := hv ((mem_Ix D i).mp hi)
    rw [vtx16_M] at this
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp this
    rw [lineOf_injective hji] at hj
    exact hj
  · rintro ⟨k, hk, rfl⟩
    have hk' := (Finset.mem_filter.mp hk).2
    rw [vtx16_M, hD]
    exact Finset.image_subset_image hk'


/-- A rational vector as a point of Euclidean space. -/
def ofQ (v : Fin 3 → ℚ) : E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun c => (v c : ℝ))

/-- The linearization of the Gram matrix of the `k`-th vertex. -/
def trQ (k : Fin 16) : Fin 3 → ℚ := ![-(triples k).1, -(triples k).2.2, -(triples k).2.1]

/-- The linearized barycentre of the vertices whose lines contain the index set `X`. -/
def bLq (X : Finset (Fin 13)) : Fin 3 → ℚ :=
  ((Finset.univ.filter fun k : Fin 16 => X ⊆ Mk k).card : ℚ)⁻¹ •
    ∑ k ∈ Finset.univ.filter (fun k : Fin 16 => X ⊆ Mk k), trQ k

theorem Lc_bpt (D : Cell) (h : T0.val ⊆ D.val) : Lc (bpt D) = ofQ (bLq (Ix D)) := by
  change Lraw (bptMat D) = _
  unfold bptMat
  rw [vertFin_above D h, Finset.card_image_of_injective _ vtx16_injective,
    Finset.sum_image (fun a _ b _ hab => vtx16_injective hab)]
  ext c
  fin_cases c <;>
    simp [Lraw, ofQ, bLq, trQ, Matrix.sum_apply, formR, vtx16, gram3, Finset.sum_neg_distrib,
      Finset.mul_sum]

end TernaryPeriodPolynomials.Argument.Lemma33.Orient
