module

public import TernaryPeriodPolynomials.Building.Good.UnimodularOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.IncidenceChains
public import TernaryPeriodPolynomials.Building.Primitive.LineUniqueness
public import Mathlib.GroupTheory.Perm.Sign

@[expose] public section


/-!
# the rational Tits building, apartments of ordered bases, the restricted subgraph

Formalized by Claude Sonnet 5.5.  And the definitions at.

Literal statements for the clauses of the "Method of proof" paragraph that had only a model-level Lean counterpart:

* `basisApartment v hv`: the oriented hexagon `L₁ → P₁₂ → L₂ → P₂₃ → L₃ → P₃₁ → L₁` of an ordered basis `v` of `ℚ³` in the unrestricted building (`basisApartment_hexagon` is the sum of its six oriented edges; `basisApartment_perm`: permuting the basis multiplies it by the sign).
* `identity_apartment_vertices_good`, `referenceApartment_columnLine`: the identity apartment is the apartment of `(e₁, e₂, e₃)` and all its vertices are good.
* `K_iff_sum_preserved`: `K` is the group of invertible integral matrices preserving the coordinate sum modulo three.
* `good_line_unique_primitive`: a good line has a unique primitive integral vector with coordinate sum one modulo three.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open TernaryPoly TernaryPoly.GoodIncidenceConnected TernaryPoly.GoodApartmentCycles

/-- The lines of the unrestricted rational Tits building (every rational line is allowed). -/
abbrev ULine := GoodIncidenceConnected.Line (fun _ => True)
/-- The planes of the unrestricted rational Tits building. -/
abbrev UPlane := GoodIncidenceConnected.Plane (fun _ => True)

section Basis

variable (v : Fin 3 → GoodIncidenceConnected.Space) (hv : LinearIndependent ℚ v)

/-- The line `L_i = ℚ v_i` of an ordered basis. -/
def basisLine (i : Fin 3) : ULine :=
  ⟨Submodule.span ℚ {v i}, finrank_span_singleton (hv.ne_zero i), trivial⟩

theorem basisLine_ne {i j : Fin 3} (hij : i ≠ j) : basisLine v hv i ≠ basisLine v hv j := by
  intro h
  have h1 : Submodule.span ℚ {v i} = Submodule.span ℚ {v j} := congrArg Subtype.val h
  have h2 : v i ∈ Submodule.span ℚ {v j} := h1 ▸ Submodule.mem_span_singleton_self _
  have h3 := hv.notMem_span_image (s := {j}) (x := i) (by simpa using hij)
  rw [Set.image_singleton] at h3
  exact h3 h2

/-- The plane `P_ij = ℚ v_i + ℚ v_j` of an ordered basis (`i ≠ j`). -/
def basisPlane (i j : Fin 3) (hij : i ≠ j) : UPlane :=
  ⟨Submodule.span ℚ {v i} ⊔ Submodule.span ℚ {v j},
    finrank_sup_of_distinct_lines _ _ (basisLine v hv i).property.1 (basisLine v hv j).property.1
      (fun h => basisLine_ne v hv hij (Subtype.ext h)),
    ⟨basisLine v hv i, le_sup_left⟩⟩

theorem basisLine_le_plane_left (i j : Fin 3) (hij : i ≠ j) :
    (basisLine v hv i).val ≤ (basisPlane v hv i j hij).val := le_sup_left

theorem basisLine_le_plane_right (i j : Fin 3) (hij : i ≠ j) :
    (basisLine v hv j).val ≤ (basisPlane v hv i j hij).val := le_sup_right

/-- The apartment of an ordered basis, as a cycle of the unrestricted incidence graph. -/
def basisApartment : Cycles (fun _ => True) :=
  apartmentCycle (fun _ => True) (basisLine v hv 0) (basisLine v hv 1) (basisLine v hv 2)

/-- **The apartment is the oriented hexagon** `L₁ → P₁₂ → L₂ → P₂₃ → L₃ → P₃₁ → L₁`: the sum of its six oriented edges, each traversed
from a line to a plane (`+`) or from a plane to a line (`-`). -/
theorem basisApartment_hexagon (h01 : (0 : Fin 3) ≠ 1) (h12 : (1 : Fin 3) ≠ 2) (h20 : (2 : Fin 3) ≠ 0) :
    (basisApartment v hv : Chains (fun _ => True)) =
      flagChain _ (basisLine v hv 0) (basisPlane v hv 0 1 h01) (basisLine_le_plane_left v hv 0 1 h01)
        - flagChain _ (basisLine v hv 1) (basisPlane v hv 0 1 h01) (basisLine_le_plane_right v hv 0 1 h01)
        + flagChain _ (basisLine v hv 1) (basisPlane v hv 1 2 h12) (basisLine_le_plane_left v hv 1 2 h12)
        - flagChain _ (basisLine v hv 2) (basisPlane v hv 1 2 h12) (basisLine_le_plane_right v hv 1 2 h12)
        + flagChain _ (basisLine v hv 2) (basisPlane v hv 2 0 h20) (basisLine_le_plane_left v hv 2 0 h20)
        - flagChain _ (basisLine v hv 0) (basisPlane v hv 2 0 h20) (basisLine_le_plane_right v hv 2 0 h20) := by
  unfold basisApartment
  rw [apartmentCycle_coe, apartmentChain,
    lineChain_of_common_plane _ _ _ (basisPlane v hv 0 1 h01) (basisLine_le_plane_left v hv 0 1 h01)
      (basisLine_le_plane_right v hv 0 1 h01),
    lineChain_of_common_plane _ _ _ (basisPlane v hv 1 2 h12) (basisLine_le_plane_left v hv 1 2 h12)
      (basisLine_le_plane_right v hv 1 2 h12),
    lineChain_of_common_plane _ _ _ (basisPlane v hv 2 0 h20) (basisLine_le_plane_left v hv 2 0 h20)
      (basisLine_le_plane_right v hv 2 0 h20)]
  abel

/-- Transposing two basis vectors reverses the orientation of the apartment. -/
theorem basisApartment_swap (x y : Fin 3) (hxy : x ≠ y) :
    basisApartment (v ∘ Equiv.swap x y) (hv.comp _ (Equiv.swap x y).injective) = -basisApartment v hv := by
  have e01 : apartmentCycle (fun _ => True) (basisLine v hv 1) (basisLine v hv 0) (basisLine v hv 2) =
      -basisApartment v hv :=
    apartmentCycle_swap (fun _ => True) (basisLine v hv 0) (basisLine v hv 1) (basisLine v hv 2)
  have e12 : apartmentCycle (fun _ => True) (basisLine v hv 0) (basisLine v hv 2) (basisLine v hv 1) =
      -basisApartment v hv :=
    (apartmentCycle_cyclic (fun _ => True) (basisLine v hv 1) (basisLine v hv 0) (basisLine v hv 2)).trans e01
  have e02 : apartmentCycle (fun _ => True) (basisLine v hv 2) (basisLine v hv 1) (basisLine v hv 0) =
      -basisApartment v hv :=
    (apartmentCycle_cyclic (fun _ => True) (basisLine v hv 0) (basisLine v hv 2) (basisLine v hv 1)).trans e12
  change apartmentCycle (fun _ => True) (basisLine v hv (Equiv.swap x y 0)) (basisLine v hv (Equiv.swap x y 1))
    (basisLine v hv (Equiv.swap x y 2)) = _
  fin_cases x <;> fin_cases y <;> first
    | exact absurd rfl hxy
    | (simp only [Equiv.swap_apply_def]; first | exact e01 | exact e12 | exact e02)

/-- **Permuting the basis multiplies the apartment by the sign of the permutation**. -/
theorem basisApartment_perm (σ : Equiv.Perm (Fin 3)) :
    basisApartment (v ∘ σ) (hv.comp _ σ.injective) = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • basisApartment v hv := by
  induction σ using Equiv.Perm.swap_induction_on generalizing v with
  | one => simp
  | swap_mul f x y hxy ih =>
    have h1 := ih (v ∘ Equiv.swap x y) (hv.comp _ (Equiv.swap x y).injective)
    have h2 := basisApartment_swap v hv x y hxy
    have e : v ∘ (Equiv.swap x y * f) = (v ∘ Equiv.swap x y) ∘ f := rfl
    simp only [e]
    rw [h1, h2]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy]

end Basis

section Identity

open ModThreeGoodAction GoodIntegralFrames

/-- The columns of the identity matrix span the coordinate lines `ℚ e_j`. -/
theorem referenceApartment_columnLine (j : Fin 3) :
    (columnLine (1 : Matrix (Fin 3) (Fin 3) ℤ) GoodUnimodularOrbit.identity_normalized j :
      GoodIncidenceConnected.Line Good).val = Submodule.span ℚ {(Pi.single j 1 : Fin 3 → ℚ)} := by
  change Submodule.span ℚ {rationalVector (fun i => (1 : Matrix (Fin 3) (Fin 3) ℤ) i j)} = _
  congr 2
  ext i
  by_cases h : i = j <;> simp [rationalVector, Matrix.one_apply, h]

/-- The identity apartment is the apartment `apartmentCycle (ℚe₁) (ℚe₂) (ℚe₃)`, and all its vertices are good. -/
theorem identity_apartment_vertices_good :
    (∀ j : Fin 3, Good (Submodule.span ℚ {(Pi.single j 1 : Fin 3 → ℚ)})) ∧
    (∀ i j : Fin 3, Good (Submodule.span ℚ {(Pi.single i 1 : Fin 3 → ℚ)} ⊔
      Submodule.span ℚ {(Pi.single j 1 : Fin 3 → ℚ)})) := by
  have hl : ∀ j : Fin 3, Good (Submodule.span ℚ {(Pi.single j 1 : Fin 3 → ℚ)}) := by
    intro j
    refine ⟨Pi.single j 1, ?_, ?_⟩
    · apply Submodule.subset_span
      ext i
      by_cases h : i = j <;> simp [rationalVector, h]
    · have : ∑ i, ((Pi.single j (1 : ℤ) : Fin 3 → ℤ) i : ZMod 3) = 1 := by
        simp [Pi.single_apply]
      rw [this]
      exact one_ne_zero
  exact ⟨hl, fun i j => (hl i).mono le_sup_left⟩

end Identity

section Group

open ModThreeGoodAction GoodIntegralNormalization PrimitiveLineUniqueness

/-- **`K` is the group of invertible integral matrices preserving the coordinate sum modulo three**. -/
theorem K_iff_sum_preserved (g : IntegralGL) :
    g ∈ K ↔ ∀ v : IntegralVector, ∑ i, ((g.val.mulVec v) i : ZMod 3) = ∑ i, (v i : ZMod 3) := by
  have key : ∀ v : IntegralVector, ∑ i, ((g.val.mulVec v) i : ZMod 3) =
      ∑ j, (∑ i, (g.val i j : ZMod 3)) * (v j : ZMod 3) := by
    intro v
    simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [mem_K]
  constructor
  · intro h v
    have hc : ∀ j, ∑ i, (g.val i j : ZMod 3) = 1 := by
      intro j
      have hj := congrFun h j
      simpa [Matrix.vecMul, dotProduct, fixedRow, reduction] using hj
    rw [key]
    simp [hc]
  · intro h
    funext j
    have := h (Pi.single j 1)
    rw [key] at this
    have hs : ∑ i, ((Pi.single j (1 : ℤ) : Fin 3 → ℤ) i : ZMod 3) = 1 := by
      simp [Pi.single_apply]
    have h2 : ∑ k, (∑ i, (g.val i k : ZMod 3)) * ((Pi.single j (1 : ℤ) : Fin 3 → ℤ) k : ZMod 3) =
        ∑ i, (g.val i j : ZMod 3) := by
      simp [Pi.single_apply]
    rw [h2, hs] at this
    simpa [Matrix.vecMul, dotProduct, fixedRow, reduction] using this

/-- **A retained line has a unique primitive vector with coordinate sum one modulo three**. -/
theorem good_line_unique_primitive (L : GoodIncidenceConnected.Line Good) :
    ∃! v : IntegralVector, Primitive v ∧ ∑ i, (v i : ZMod 3) = 1 ∧ Submodule.span ℚ {rationalVector v} = L.val := by
  obtain ⟨v, hp, -, -, hs, hr⟩ := good_line_primitive_generator L.property.1 L.property.2
  refine ⟨v, ⟨hp, hr, hs⟩, ?_⟩
  rintro w ⟨hpw, hrw, hsw⟩
  exact primitive_eq_of_residue_one_of_span_eq hpw hp hrw hr (hsw.trans hs.symm)

end Group

end TernaryPeriodPolynomials.Argument.Identities
