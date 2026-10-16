module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.ChartValue

@[expose] public section


/-!
# Orientation transport: the staircase (Eilenberg-Zilber) chain of tetrahedron times triangle

The product of the reference tetrahedron `tetraV` (scale `4`) and the reference triangle `rtri` (scale `3`) is triangulated
by the ten lattice paths of the `4 × 3` grid, indexed by the positions `s < t` of the two steps in the second factor
(`stairSimp s t`, sign `(-1)^(s+t+1)`); `stair` is the signed sum.  Its boundary is carried by `UA` and `UB`
(`stair_boundary_mem`): the interior faces (a diagonal step) cancel in pairs (`interior_sum_zero`, by a finite check
`inv_ok` of the swapping involution), and every other face omits a row or a column of the lattice and so lies over a
facet of the tetrahedron (in `UB`) or an edge of the triangle (in `UA`).  For Thom cochains (`ThomPair`) the pairing of `stair`
is `lamPos · lam2` (`Pair_stair`): of the ten simplices only the path with the two second-factor steps first has a
non-degenerate back tetrahedron and front triangle; the other nine pair to zero because a Thom cochain vanishes on an
affine simplex all of whose vertices lie in a facet of the reference tetrahedron (resp. an edge of the triangle).

Formalized by Claude Sonnet 5.5.
-/

open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33.Orient
open TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.ContractibleSingularHomology TernaryPoly.RationalRelativeSingular

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

/-! ### Combinatorics of the staircase triangulation of a tetrahedron times a triangle -/

/-- Number of `b`-steps among the first `k` steps of the lattice path with `b`-steps at positions `s < t`. -/
def jc (s t k : ℕ) : ℕ := (if s < k then 1 else 0) + (if t < k then 1 else 0)

/-- Lattice point of vertex `k` of the path with `b`-steps at `s < t`. -/
def gp (s t k : ℕ) : ℕ × ℕ := (k - jc s t k, jc s t k)

/-- `Fin.succAbove` on natural numbers. -/
def sa (k m : ℕ) : ℕ := if m < k then m else m + 1

/-- The lattice tuple of the face omitting vertex `k`. -/
def fg (s t k m : ℕ) : ℕ × ℕ := gp s t (sa k m)

def inB (s t p : ℕ) : Bool := decide (p = s ∨ p = t)

/-- A face is interior if exactly one of the steps `k-1`, `k` is a `b`-step. -/
def interior (s t k : ℕ) : Bool := decide (0 < k ∧ k < 5 ∧ (inB s t (k - 1) ≠ inB s t k))

def newB (s t k p : ℕ) : Bool :=
  if p = k - 1 then inB s t k else if p = k then inB s t (k - 1) else inB s t p

def newS (s t k : ℕ) : ℕ := ((List.range 5).find? (fun p => newB s t k p)).getD 0
def newT (s t k : ℕ) : ℕ := ((List.range 5).filter (fun p => newB s t k p)).getLastD 0

def chk (s t k : ℕ) : Bool :=
  !(decide (s < t) && interior s t k) ||
    (decide (newS s t k < newT s t k) && decide (newT s t k < 5) &&
     (List.range 5).all (fun m => decide (fg (newS s t k) (newT s t k) k m = fg s t k m)) &&
     decide (newS (newS s t k) (newT s t k) k = s) && decide (newT (newS s t k) (newT s t k) k = t) &&
     interior (newS s t k) (newT s t k) k &&
     decide ((newS s t k + newT s t k + 1 + k + (s + t + 1 + k)) % 2 = 1))

theorem inv_ok :
    (List.range 5).all (fun s => (List.range 5).all (fun t => (List.range 6).all (fun k => chk s t k))) = true := by
  decide +kernel

/-- A non-interior face omits a lattice row or column entirely. -/
def skipI (s t k v : ℕ) : Bool := decide (v < 4) && (List.range 5).all (fun m => decide ((fg s t k m).1 ≠ v))
def skipJ (s t k v : ℕ) : Bool := decide (v < 3) && (List.range 5).all (fun m => decide ((fg s t k m).2 ≠ v))

def chk2 (s t k : ℕ) : Bool :=
  !(decide (s < t) && !interior s t k) ||
    ((List.range 4).any (fun v => skipI s t k v) || (List.range 3).any (fun v => skipJ s t k v))

theorem boundary_ok :
    (List.range 5).all (fun s => (List.range 5).all (fun t => (List.range 6).all (fun k => chk2 s t k))) = true := by
  decide +kernel

def chk3 (s t k : ℕ) : Bool :=
  !(decide (s < t)) ||
    ((List.range 5).all (fun m => decide ((fg s t k m).1 ≤ 3 ∧ (fg s t k m).2 ≤ 2)))

theorem range_ok :
    (List.range 5).all (fun s => (List.range 5).all (fun t => (List.range 6).all (fun k => chk3 s t k))) = true := by
  decide +kernel

/-! ### The staircase chain -/

local notation "E5" => EuclideanSpace ℝ (Fin 5)
local notation "X5" => TopCat.of (EuclideanSpace ℝ (Fin 5))

/-- The point of `ℝ⁵` at lattice point `(i, j)` of the product of the reference tetrahedron (`i ≤ 3`) and triangle
(`j ≤ 2`); out-of-range indices are clamped. -/
def vertN (g : ℕ × ℕ) : E5 :=
  prodEL (tetraV ⟨min g.1 3, by omega⟩, rtri ⟨min g.2 2, by omega⟩)

/-- The vertex `kk` of the staircase simplex with `b`-steps at positions `s < t`. -/
def Vst (s t kk : ℕ) : E5 := vertN (gp s t kk)

/-- The staircase simplex of the path with `b`-steps at `s < t`. -/
def stairSimp (s t : ℕ) : singularSimplices X5 5 := affSimp 5 (fun k : Fin 6 => Vst s t k.val)

/-- The index set of staircase simplices: pairs `s < t` of positions of the two `b`-steps. -/
def pairs : Finset (ℕ × ℕ) := (Finset.range 5 ×ˢ Finset.range 5).filter (fun p => p.1 < p.2)

/-- **The staircase (Eilenberg-Zilber) chain of the product of the reference tetrahedron and triangle.** -/
def stair : singularChainGroup ℚ X5 5 :=
  ∑ p ∈ pairs, ((-1 : ℚ) ^ (p.1 + p.2 + 1)) • chainGenerator ℚ X5 5 (stairSimp p.1 p.2)

theorem succAbove_val (k : Fin 6) (m : Fin 5) : ((k.succAbove m : Fin 6) : ℕ) = sa k.val m.val := by
  unfold sa
  by_cases h : m.val < k.val
  · rw [ite_eq_left h]
    have : m.castSucc < k := h
    rw [Fin.succAbove_of_castSucc_lt _ _ this]
    rfl
  · rw [ite_eq_right h]
    have : k ≤ m.castSucc := not_lt.mp h
    rw [Fin.succAbove_of_le_castSucc _ _ this]
    rfl

/-- The face of a staircase simplex omitting vertex `k`. -/
def stairFace (s t k : ℕ) : singularSimplices X5 4 :=
  affSimp 4 (fun m : Fin 5 => Vst s t (sa k m.val))

theorem boundary_stairSimp (s t : ℕ) :
    (singularBoundary ℚ X5 4).hom (chainGenerator ℚ X5 5 (stairSimp s t)) =
      ∑ k ∈ Finset.range 6, ((-1 : ℚ) ^ k) • chainGenerator ℚ X5 4 (stairFace s t k) := by
  rw [singularBoundary_chainGenerator_formula]
  rw [← Fin.sum_univ_eq_sum_range (fun k => ((-1 : ℚ) ^ k) • chainGenerator ℚ X5 4 (stairFace s t k)) 6]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold stairSimp
  rw [faceSimplex_affSimp]
  congr 2
  unfold stairFace
  congr 1
  funext m
  show Vst s t ((k.succAbove m : Fin 6) : ℕ) = Vst s t (sa k.val m.val)
  rw [succAbove_val]

theorem chk_spec {s t k : ℕ} (hs : s < 5) (ht : t < 5) (hk : k < 6) (hst : s < t) (hint : interior s t k = true) :
    newS s t k < newT s t k ∧ newT s t k < 5 ∧
    (∀ m < 5, fg (newS s t k) (newT s t k) k m = fg s t k m) ∧
    newS (newS s t k) (newT s t k) k = s ∧ newT (newS s t k) (newT s t k) k = t ∧
    interior (newS s t k) (newT s t k) k = true ∧
    (newS s t k + newT s t k + 1 + k + (s + t + 1 + k)) % 2 = 1 := by
  have h := inv_ok
  rw [List.all_eq_true] at h
  have h1 := h s (List.mem_range.mpr hs)
  rw [List.all_eq_true] at h1
  have h2 := h1 t (List.mem_range.mpr ht)
  rw [List.all_eq_true] at h2
  have h3 := h2 k (List.mem_range.mpr hk)
  unfold chk at h3
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    Bool.and_eq_true, decide_eq_true_eq] at h3
  rcases h3 with h3 | h3
  · exfalso
    rcases h3 with h3 | h3
    · exact h3 hst
    · rw [hint] at h3; exact absurd h3 (by simp)
  · obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := h3
    refine ⟨a1, a2, ?_, a4, a5, a6, a7⟩
    intro m hm
    rw [List.all_eq_true] at a3
    exact decide_eq_true_iff.mp (a3 m (List.mem_range.mpr hm))

theorem stairFace_eq {s t s' t' k : ℕ} (h : ∀ m < 5, fg s' t' k m = fg s t k m) :
    stairFace s' t' k = stairFace s t k := by
  unfold stairFace
  congr 1
  funext m
  show vertN (gp s' t' (sa k m.val)) = vertN (gp s t (sa k m.val))
  exact congrArg vertN (h m.val m.isLt)

/-- The faces of the staircase simplices with their signs. -/
def faceTerm (x : (ℕ × ℕ) × ℕ) : singularChainGroup ℚ X5 4 :=
  ((-1 : ℚ) ^ (x.1.1 + x.1.2 + 1 + x.2)) • chainGenerator ℚ X5 4 (stairFace x.1.1 x.1.2 x.2)

/-- The set of all (path, omitted vertex) pairs. -/
def triples : Finset ((ℕ × ℕ) × ℕ) := pairs ×ˢ Finset.range 6

theorem boundary_stair :
    (singularBoundary ℚ X5 4).hom stair = ∑ x ∈ triples, faceTerm x := by
  unfold stair triples
  rw [map_sum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_smul, boundary_stairSimp, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold faceTerm
  simp only [smul_smul, pow_add]

theorem interior_sum_zero :
    ∑ x ∈ triples.filter (fun x => interior x.1.1 x.1.2 x.2 = true), faceTerm x = 0 := by
  refine Finset.sum_involution (fun x _ => ((newS x.1.1 x.1.2 x.2, newT x.1.1 x.1.2 x.2), x.2)) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxT, hint⟩ := Finset.mem_filter.mp hx
    obtain ⟨⟨s, t⟩, k⟩ := x
    simp only [triples, pairs, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hxT hint
    obtain ⟨⟨⟨hs, ht⟩, hst⟩, hk⟩ := hxT
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := chk_spec hs ht hk hst hint
    unfold faceTerm
    simp only
    rw [stairFace_eq (s := s) (t := t) a3]
    rw [← add_smul]
    have hodd : Odd ((newS s t k + newT s t k + 1 + k) + (s + t + 1 + k)) := by
      rw [Nat.odd_iff]; exact a7
    have hprod : ((-1 : ℚ) ^ (newS s t k + newT s t k + 1 + k)) * ((-1 : ℚ) ^ (s + t + 1 + k)) = -1 := by
      rw [← pow_add]; exact hodd.neg_one_pow
    have hsq : ((-1 : ℚ) ^ (s + t + 1 + k)) * ((-1 : ℚ) ^ (s + t + 1 + k)) = 1 := by
      rw [← pow_add, ← two_mul]; exact (Even.neg_one_pow (even_two_mul _))
    have hpar : (-1 : ℚ) ^ (s + t + 1 + k) + (-1 : ℚ) ^ (newS s t k + newT s t k + 1 + k) = 0 := by
      have : (-1 : ℚ) ^ (newS s t k + newT s t k + 1 + k) = -(-1 : ℚ) ^ (s + t + 1 + k) := by
        calc (-1 : ℚ) ^ (newS s t k + newT s t k + 1 + k)
            = (-1 : ℚ) ^ (newS s t k + newT s t k + 1 + k) * (((-1 : ℚ) ^ (s + t + 1 + k)) * ((-1 : ℚ) ^ (s + t + 1 + k))) := by
              rw [hsq, mul_one]
          _ = (((-1 : ℚ) ^ (newS s t k + newT s t k + 1 + k)) * ((-1 : ℚ) ^ (s + t + 1 + k))) * ((-1 : ℚ) ^ (s + t + 1 + k)) := by ring
          _ = -(-1 : ℚ) ^ (s + t + 1 + k) := by rw [hprod]; ring
      rw [this]; ring
    rw [hpar, zero_smul]
  · intro x hx _ heq
    obtain ⟨hxT, hint⟩ := Finset.mem_filter.mp hx
    obtain ⟨⟨s, t⟩, k⟩ := x
    simp only [triples, pairs, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hxT hint
    obtain ⟨⟨⟨hs, ht⟩, hst⟩, hk⟩ := hxT
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := chk_spec hs ht hk hst hint
    have e1 : newS s t k = s := congrArg (fun y => y.1.1) heq
    have e2 : newT s t k = t := congrArg (fun y => y.1.2) heq
    rw [e1, e2] at a7
    omega
  · intro x hx
    obtain ⟨hxT, hint⟩ := Finset.mem_filter.mp hx
    obtain ⟨⟨s, t⟩, k⟩ := x
    simp only [triples, pairs, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hxT hint ⊢
    obtain ⟨⟨⟨hs, ht⟩, hst⟩, hk⟩ := hxT
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := chk_spec hs ht hk hst hint
    refine ⟨?_, a6⟩
    omega
  · intro x hx
    obtain ⟨hxT, hint⟩ := Finset.mem_filter.mp hx
    obtain ⟨⟨s, t⟩, k⟩ := x
    simp only [triples, pairs, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hxT hint
    obtain ⟨⟨⟨hs, ht⟩, hst⟩, hk⟩ := hxT
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := chk_spec hs ht hk hst hint
    simp only [a4, a5]

/-! ### Non-interior faces lie in `UA` or `UB` -/

theorem affMapN_coord3 (n : ℕ) (w : Fin (n + 1) → R3) (t : Delta n) (j : Fin 3) :
    affMapN n w t j = ∑ m, t.weights m * w m j := by
  simp [affMapN]

theorem affMapN_coord2 (n : ℕ) (w : Fin (n + 1) → R2) (t : Delta n) (j : Fin 2) :
    affMapN n w t j = ∑ m, t.weights m * w m j := by
  simp [affMapN]

theorem far3_of_functional {n : ℕ} (c0 c1 c2 : ℝ) (idx : Fin (n + 1) → Fin 4)
    (key : ∀ m, c0 * tetraV (idx m) 0 + c1 * tetraV (idx m) 1 + c2 * tetraV (idx m) 2 = 4)
    (hh : c0 ^ 2 + c1 ^ 2 + c2 ^ 2 < 4 ^ 2) (t : Delta n) :
    1 < ‖affMapN n (fun m => tetraV (idx m)) t‖ := by
  refine norm_gt_one_of3 _ c0 c1 c2 4 ?_ hh
  have hs : ∑ m, t.weights m = 1 := t.total_of_fintype
  simp only [affMapN_coord3, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have : ∀ m, c0 * (t.weights m * tetraV (idx m) 0) + c1 * (t.weights m * tetraV (idx m) 1)
      + c2 * (t.weights m * tetraV (idx m) 2) = t.weights m * 4 := by
    intro m
    have := key m
    linear_combination (t.weights m) * this
  simp only [this]
  rw [← Finset.sum_mul, hs, one_mul]

theorem pi_far {n : ℕ} (v : Fin 4) (idx : Fin (n + 1) → Fin 4) (hidx : ∀ m, idx m ≠ v) (t : Delta n) :
    1 < ‖affMapN n (fun m => tetraV (idx m)) t‖ := by
  fin_cases v
  · refine far3_of_functional 1 (-3) 1 idx ?_ (by norm_num) t
    intro m
    have := hidx m
    generalize idx m = u at this ⊢
    fin_cases u <;> simp_all [tetraV, rref, rv, mk3]
    all_goals norm_num
  · refine far3_of_functional (-3) 1 1 idx ?_ (by norm_num) t
    intro m
    have := hidx m
    generalize idx m = u at this ⊢
    fin_cases u <;> simp_all [tetraV, rref, rv, mk3]
    all_goals norm_num
  · refine far3_of_functional 1 1 (-3) idx ?_ (by norm_num) t
    intro m
    have := hidx m
    generalize idx m = u at this ⊢
    fin_cases u <;> simp_all [tetraV, rref, rv, mk3]
    all_goals norm_num
  · refine far3_of_functional 1 1 1 idx ?_ (by norm_num) t
    intro m
    have := hidx m
    generalize idx m = u at this ⊢
    fin_cases u <;> simp_all [tetraV, rref, rv, mk3]

theorem far2_of_functional {n : ℕ} (c0 c1 : ℝ) (idx : Fin (n + 1) → Fin 3)
    (key : ∀ m, c0 * rtri (idx m) 0 + c1 * rtri (idx m) 1 = 3)
    (hh : c0 ^ 2 + c1 ^ 2 < 3 ^ 2) (t : Delta n) :
    1 < ‖affMapN n (fun m => rtri (idx m)) t‖ := by
  refine norm_gt_one_of2 _ c0 c1 3 ?_ hh
  have hs : ∑ m, t.weights m = 1 := t.total_of_fintype
  simp only [affMapN_coord2, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  have : ∀ m, c0 * (t.weights m * rtri (idx m) 0) + c1 * (t.weights m * rtri (idx m) 1)
      = t.weights m * 3 := by
    intro m
    have := key m
    linear_combination (t.weights m) * this
  simp only [this]
  rw [← Finset.sum_mul, hs, one_mul]

theorem rho_far {n : ℕ} (v : Fin 3) (idx : Fin (n + 1) → Fin 3) (hidx : ∀ m, idx m ≠ v) (t : Delta n) :
    1 < ‖affMapN n (fun m => rtri (idx m)) t‖ := by
  fin_cases v
  · refine far2_of_functional (-2) 1 idx ?_ (by norm_num) t
    intro m
    have := hidx m
    generalize idx m = u at this ⊢
    fin_cases u <;> simp_all [rtri, rt, mk2]
    all_goals norm_num
  · refine far2_of_functional 1 (-2) idx ?_ (by norm_num) t
    intro m
    have := hidx m
    generalize idx m = u at this ⊢
    fin_cases u <;> simp_all [rtri, rt, mk2]
    all_goals norm_num
  · refine far2_of_functional 1 1 idx ?_ (by norm_num) t
    intro m
    have := hidx m
    generalize idx m = u at this ⊢
    fin_cases u <;> simp_all [rtri, rt, mk2]

theorem range_spec {s t k : ℕ} (hs : s < 5) (ht : t < 5) (hk : k < 6) (hst : s < t) :
    ∀ m < 5, (fg s t k m).1 ≤ 3 ∧ (fg s t k m).2 ≤ 2 := by
  have h := range_ok
  rw [List.all_eq_true] at h
  have h1 := h s (List.mem_range.mpr hs)
  rw [List.all_eq_true] at h1
  have h2 := h1 t (List.mem_range.mpr ht)
  rw [List.all_eq_true] at h2
  have h3 := h2 k (List.mem_range.mpr hk)
  unfold chk3 at h3
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h3
  rcases h3 with h3 | h3
  · exact absurd hst h3
  · intro m hm
    rw [List.all_eq_true] at h3
    exact decide_eq_true_iff.mp (h3 m (List.mem_range.mpr hm))

theorem boundary_spec {s t k : ℕ} (hs : s < 5) (ht : t < 5) (hk : k < 6) (hst : s < t)
    (hni : interior s t k = false) :
    (∃ v, skipI s t k v = true) ∨ (∃ v, skipJ s t k v = true) := by
  have h := boundary_ok
  rw [List.all_eq_true] at h
  have h1 := h s (List.mem_range.mpr hs)
  rw [List.all_eq_true] at h1
  have h2 := h1 t (List.mem_range.mpr ht)
  rw [List.all_eq_true] at h2
  have h3 := h2 k (List.mem_range.mpr hk)
  unfold chk2 at h3
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    Bool.not_eq_false', List.any_eq_true, List.mem_range] at h3
  rcases h3 with (h3 | h3) | h3
  · exact absurd hst h3
  · rw [hni] at h3; exact absurd h3 (by simp)
  · rcases h3 with ⟨v, _, hv⟩ | ⟨v, _, hv⟩
    · exact Or.inl ⟨v, hv⟩
    · exact Or.inr ⟨v, hv⟩

theorem piE_affMapN (n : ℕ) (w : Fin (n + 1) → EuclideanSpace ℝ (Fin 5)) (x : Delta n) :
    piE (affMapN n w x) = affMapN n (fun m => piE (w m)) x := by
  simp [affMapN, map_sum, map_smul]

theorem rhoE_affMapN (n : ℕ) (w : Fin (n + 1) → EuclideanSpace ℝ (Fin 5)) (x : Delta n) :
    rhoE (affMapN n w x) = affMapN n (fun m => rhoE (w m)) x := by
  simp [affMapN, map_sum, map_smul]

theorem skipI_spec {s t k v : ℕ} (h : skipI s t k v = true) : v < 4 ∧ ∀ m < 5, (fg s t k m).1 ≠ v := by
  unfold skipI at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1, fun m hm => by simpa using h.2 m hm⟩

theorem skipJ_spec {s t k v : ℕ} (h : skipJ s t k v = true) : v < 3 ∧ ∀ m < 5, (fg s t k m).2 ≠ v := by
  unfold skipJ at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1, fun m hm => by simpa using h.2 m hm⟩

theorem stairFace_sub_UB {s t k v : ℕ} (hs : s < 5) (ht : t < 5) (hk : k < 6) (hst : s < t)
    (hv : skipI s t k v = true) : IsSubordinate UB (stairFace s t k) := by
  obtain ⟨hv4, hvm⟩ := skipI_spec hv
  have hr := range_spec hs ht hk hst
  refine isSubordinate_affSimp (fun x => ?_)
  show (1 / 4 : ℝ) < ‖piE (affMapN 4 (fun m : Fin 5 => Vst s t (sa k m.val)) x)‖
  rw [piE_affMapN]
  have key : (fun m : Fin 5 => piE (Vst s t (sa k m.val))) =
      fun m : Fin 5 => tetraV ⟨min (fg s t k m.val).1 3, by omega⟩ := by
    funext m
    show piE (vertN (fg s t k m.val)) = _
    unfold vertN
    exact piE_prodEL _
  rw [key]
  have := pi_far ⟨v, hv4⟩ (fun m : Fin 5 => ⟨min (fg s t k m.val).1 3, by omega⟩) (by
    intro m hm
    have h1 := hvm m.val m.isLt
    have h2 := (hr m.val m.isLt).1
    apply h1
    have := congrArg Fin.val hm
    simp only at this
    omega) x
  linarith

theorem stairFace_sub_UA {s t k v : ℕ} (hs : s < 5) (ht : t < 5) (hk : k < 6) (hst : s < t)
    (hv : skipJ s t k v = true) : IsSubordinate UA (stairFace s t k) := by
  obtain ⟨hv3, hvm⟩ := skipJ_spec hv
  have hr := range_spec hs ht hk hst
  refine isSubordinate_affSimp (fun x => ?_)
  show (1 / 4 : ℝ) < ‖rhoE (affMapN 4 (fun m : Fin 5 => Vst s t (sa k m.val)) x)‖
  rw [rhoE_affMapN]
  have key : (fun m : Fin 5 => rhoE (Vst s t (sa k m.val))) =
      fun m : Fin 5 => rtri ⟨min (fg s t k m.val).2 2, by omega⟩ := by
    funext m
    show rhoE (vertN (fg s t k m.val)) = _
    unfold vertN
    exact rhoE_prodEL _
  rw [key]
  have := rho_far ⟨v, hv3⟩ (fun m : Fin 5 => ⟨min (fg s t k m.val).2 2, by omega⟩) (by
    intro m hm
    have h1 := hvm m.val m.isLt
    have h2 := (hr m.val m.isLt).2
    apply h1
    have := congrArg Fin.val hm
    simp only at this
    omega) x
  linarith

theorem faceTerm_mem {x : (ℕ × ℕ) × ℕ} (hx : x ∈ triples) (hni : interior x.1.1 x.1.2 x.2 = false) :
    faceTerm x ∈ subChainSubmodule ℚ X5 UA 4 ⊔ subChainSubmodule ℚ X5 UB 4 := by
  obtain ⟨⟨s, t⟩, k⟩ := x
  simp only [triples, pairs, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx
  obtain ⟨⟨⟨hs, ht⟩, hst⟩, hk⟩ := hx
  rcases boundary_spec hs ht hk hst hni with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact Submodule.mem_sup_right (Submodule.smul_mem _ _
      (chainGenerator_mem_subChainSubmodule (stairFace_sub_UB hs ht hk hst hv)))
  · exact Submodule.mem_sup_left (Submodule.smul_mem _ _
      (chainGenerator_mem_subChainSubmodule (stairFace_sub_UA hs ht hk hst hv)))

/-- **The boundary of the staircase chain is carried by `UA` and `UB`.** -/
theorem stair_boundary_mem :
    (singularBoundary ℚ X5 4).hom stair ∈ subChainSubmodule ℚ X5 UA 4 ⊔ subChainSubmodule ℚ X5 UB 4 := by
  rw [boundary_stair, ← Finset.sum_filter_add_sum_filter_not triples
    (fun x => interior x.1.1 x.1.2 x.2 = true), interior_sum_zero, zero_add]
  refine Submodule.sum_mem _ (fun x hx => ?_)
  obtain ⟨hxT, hni⟩ := Finset.mem_filter.mp hx
  exact faceTerm_mem hxT (by simpa using hni)

/-! ### The pairing of the staircase chain -/

variable {y₀ : (chains R3).X 3 →ₗ[ℚ] ℚ} {θ₀ : (chains R2).X 2 →ₗ[ℚ] ℚ}

theorem degR3_eq_zero_of_avoids (c : (chains R3).X 3)
    (h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0) (h0 : (locR3.f 3).hom c = 0) :
    degR3 c h = 0 := by
  have h00 : ((localChains 3).d 3 2).hom ((locR3.f 3).hom (0 : (chains R3).X 3)) = 0 := by simp
  rw [degR3_eq_of_sub c 0 h h00 0 (by rw [h0]; simp), degR3_zero]

theorem degR2_eq_zero_of_avoids (c : (chains R2).X 2)
    (h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0) (h0 : (locR2.f 2).hom c = 0) :
    degR2 c h = 0 := by
  have h00 : ((localChains 2).d 2 1).hom ((locR2.f 2).hom (0 : (chains R2).X 2)) = 0 := by simp
  rw [degR2_eq_of_sub c 0 h h00 0 (by rw [h0]; simp), degR2_zero]

theorem exists_missing {α : Type} [Fintype α] [DecidableEq α] (u : α → α) (hu : ¬ Function.Injective u) :
    ∃ v, ∀ m, u m ≠ v := by
  by_contra hcon
  push Not at hcon
  exact hu (Finite.injective_iff_surjective.mpr (fun v => by
    obtain ⟨m, hm⟩ := hcon v
    exact ⟨m, hm⟩))

theorem y0_degenerate (H : ThomPair y₀ θ₀) (u : Fin 4 → Fin 4) (hu : ¬ Function.Injective u) :
    y₀ (chainGenerator ℚ (TopCat.of R3) 3 (affSimp 3 (fun m => tetraV (u m)))) = 0 := by
  obtain ⟨v, hv⟩ := exists_missing u hu
  have hfaces : ∀ k : Fin 4, ∀ t, affMapN 2 (fun i => tetraV (u (k.succAbove i))) t ∈
      ({v : R3 | 1 / 4 < ‖v‖} : Set R3) := by
    intro k t
    have := pi_far v (fun i : Fin 3 => u (k.succAbove i)) (fun i => hv _) t
    show (1 / 4 : ℝ) < ‖affMapN 2 (fun i => tetraV (u (k.succAbove i))) t‖
    linarith
  have hmem := boundary_affSimp_mem {v : R3 | 1 / 4 < ‖v‖} 2 (fun m => tetraV (u m)) hfaces
  obtain ⟨h, h'⟩ := H.y_deg _ hmem
  rw [h']
  refine degR3_eq_zero_of_avoids _ h ?_
  refine locR3_sub_zero (U := ({0} : Set R3)ᶜ) subset_rfl 3 ?_
  refine chainGenerator_mem_subChainSubmodule (isSubordinate_affSimp (fun t => ?_))
  have := pi_far v (fun i : Fin 4 => u i) (fun i => hv _) t
  intro h0
  rw [Set.mem_singleton_iff] at h0
  rw [h0, norm_zero] at this
  exact absurd this (by norm_num)

theorem t0_degenerate (H : ThomPair y₀ θ₀) (u : Fin 3 → Fin 3) (hu : ¬ Function.Injective u) :
    θ₀ (chainGenerator ℚ (TopCat.of R2) 2 (affSimp 2 (fun m => rtri (u m)))) = 0 := by
  obtain ⟨v, hv⟩ := exists_missing u hu
  have hfaces : ∀ k : Fin 3, ∀ t, affMapN 1 (fun i => rtri (u (k.succAbove i))) t ∈
      ({v : R2 | 1 / 4 < ‖v‖} : Set R2) := by
    intro k t
    have := rho_far v (fun i : Fin 2 => u (k.succAbove i)) (fun i => hv _) t
    show (1 / 4 : ℝ) < ‖affMapN 1 (fun i => rtri (u (k.succAbove i))) t‖
    linarith
  have hmem := boundary_affSimp_mem {v : R2 | 1 / 4 < ‖v‖} 1 (fun m => rtri (u m)) hfaces
  obtain ⟨h, h'⟩ := H.t_deg _ hmem
  rw [h']
  refine degR2_eq_zero_of_avoids _ h ?_
  refine locR2_sub_zero (U := ({0} : Set R2)ᶜ) subset_rfl 2 ?_
  refine chainGenerator_mem_subChainSubmodule (isSubordinate_affSimp (fun t => ?_))
  have := rho_far v (fun i : Fin 3 => u i) (fun i => hv _) t
  intro h0
  rw [Set.mem_singleton_iff] at h0
  rw [h0, norm_zero] at this
  exact absurd this (by norm_num)

theorem push_back_stair (s t : ℕ) :
    pushSimplex piEHom 3 (backSimplex X5 2 3 (stairSimp s t)) =
      affSimp 3 (fun m : Fin 4 => piE (Vst s t (m.val + 2))) := by
  unfold stairSimp
  rw [backSimplex_affSimp]
  have := pushSimplex_affSimp (V := EuclideanSpace ℝ (Fin 5)) (W := R3) piE piE_cont 3
    (fun i : Fin 4 => Vst s t (i.val + 2))
  exact this

theorem push_front_stair (s t : ℕ) :
    pushSimplex rhoEHom 2 (frontSimplex X5 2 3 (stairSimp s t)) =
      affSimp 2 (fun m : Fin 3 => rhoE (Vst s t m.val)) := by
  unfold stairSimp
  rw [frontSimplex_affSimp]
  have := pushSimplex_affSimp (V := EuclideanSpace ℝ (Fin 5)) (W := R2) rhoE rhoE_cont 2
    (fun i : Fin 3 => Vst s t i.val)
  exact this

def chk4 (s t : ℕ) : Bool :=
  !(decide (s < t)) ||
    (((List.range 6).all (fun k => decide ((gp s t k).1 ≤ 3 ∧ (gp s t k).2 ≤ 2))) &&
      ((decide (s = 0 ∧ t = 1)) ||
        (List.range 3).any (fun m => decide ((gp s t (m + 2)).1 = (gp s t (m + 3)).1)) ||
        (List.range 2).any (fun m => decide ((gp s t m).2 = (gp s t (m + 1)).2))))

theorem chk4_ok : (List.range 5).all (fun s => (List.range 5).all (fun t => chk4 s t)) = true := by
  decide +kernel

theorem chk4_spec {s t : ℕ} (hs : s < 5) (ht : t < 5) (hst : s < t) :
    (∀ k < 6, (gp s t k).1 ≤ 3 ∧ (gp s t k).2 ≤ 2) ∧
    ((s = 0 ∧ t = 1) ∨ (∃ m < 3, (gp s t (m + 2)).1 = (gp s t (m + 3)).1) ∨
      (∃ m < 2, (gp s t m).2 = (gp s t (m + 1)).2)) := by
  have h := chk4_ok
  rw [List.all_eq_true] at h
  have h1 := h s (List.mem_range.mpr hs)
  rw [List.all_eq_true] at h1
  have h2 := h1 t (List.mem_range.mpr ht)
  unfold chk4 at h2
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true,
    List.all_eq_true, List.any_eq_true, List.mem_range, decide_eq_true_eq] at h2
  rcases h2 with h2 | ⟨h2, h3⟩
  · exact absurd hst h2
  · refine ⟨fun k hk => h2 k hk, ?_⟩
    rcases h3 with (h3 | ⟨m, hm, h3⟩) | ⟨m, hm, h3⟩
    · exact Or.inl h3
    · exact Or.inr (Or.inl ⟨m, hm, h3⟩)
    · exact Or.inr (Or.inr ⟨m, hm, h3⟩)

theorem piE_Vst (s t kk : ℕ) : piE (Vst s t kk) = tetraV ⟨min (gp s t kk).1 3, by omega⟩ := by
  unfold Vst vertN
  exact piE_prodEL _

theorem rhoE_Vst (s t kk : ℕ) : rhoE (Vst s t kk) = rtri ⟨min (gp s t kk).2 2, by omega⟩ := by
  unfold Vst vertN
  exact rhoE_prodEL _

/-- **The pairing of a staircase simplex**: `lamPos · lam2` for the unique path with the two `b`-steps first, and `0`
for the other nine. -/
theorem Pair_stairSimp (H : ThomPair y₀ θ₀) {s t : ℕ} (hs : s < 5) (ht : t < 5) (hst : s < t) :
    Pair y₀ θ₀ (chainGenerator ℚ X5 (2 + 3) (stairSimp s t)) =
      if s = 0 ∧ t = 1 then lamPos * lam2 else 0 := by
  unfold Pair
  rw [capPairF_generator]
  show yE y₀ _ * thE θ₀ _ = _
  unfold yE thE
  rw [LinearMap.comp_apply, LinearMap.comp_apply, singularChainMap_generator, singularChainMap_generator,
    push_back_stair, push_front_stair]
  obtain ⟨hr, hcases⟩ := chk4_spec hs ht hst
  have hback : (fun m : Fin 4 => piE (Vst s t (m.val + 2))) =
      fun m : Fin 4 => tetraV ⟨min (gp s t (m.val + 2)).1 3, by omega⟩ := by
    funext m; exact piE_Vst _ _ _
  have hfront : (fun m : Fin 3 => rhoE (Vst s t m.val)) =
      fun m : Fin 3 => rtri ⟨min (gp s t m.val).2 2, by omega⟩ := by
    funext m; exact rhoE_Vst _ _ _
  rw [hback, hfront]
  by_cases h01 : s = 0 ∧ t = 1
  · obtain ⟨rfl, rfl⟩ := h01
    rw [ite_eq_left ⟨rfl, rfl⟩]
    have e1 : (fun m : Fin 4 => tetraV ⟨min (gp 0 1 (m.val + 2)).1 3, by omega⟩) = tetraV := by
      funext m; fin_cases m <;> rfl
    have e2 : (fun m : Fin 3 => rtri ⟨min (gp 0 1 m.val).2 2, by omega⟩) = rtri := by
      funext m; fin_cases m <;> rfl
    rw [e1, e2, thom3_tetra y₀ H.y_deg1, thom2_tri θ₀ H.t_deg1]
  · rw [ite_eq_right h01]
    rcases hcases with h | ⟨m, hm, he⟩ | ⟨m, hm, he⟩
    · exact absurd h h01
    · have hu : ¬ Function.Injective
          (fun m : Fin 4 => (⟨min (gp s t (m.val + 2)).1 3, by omega⟩ : Fin 4)) := by
        intro hinj
        have h3 : m + 1 + 2 = m + 3 := by omega
        have := @hinj ⟨m, by omega⟩ ⟨m + 1, by omega⟩ (by
          apply Fin.ext
          show min (gp s t (m + 2)).1 3 = min (gp s t (m + 1 + 2)).1 3
          rw [h3, he])
        have := congrArg Fin.val this
        simp at this
      rw [y0_degenerate H _ hu, zero_mul]
    · have hu : ¬ Function.Injective
          (fun m : Fin 3 => (⟨min (gp s t m.val).2 2, by omega⟩ : Fin 3)) := by
        intro hinj
        have := @hinj ⟨m, by omega⟩ ⟨m + 1, by omega⟩ (by
          apply Fin.ext
          show min (gp s t m).2 2 = min (gp s t (m + 1)).2 2
          rw [he])
        have := congrArg Fin.val this
        simp at this
      rw [t0_degenerate H _ hu, mul_zero]

/-- **The pairing of the Thom cochains on the staircase chain**: `lamPos · lam2`. -/
theorem Pair_stair (H : ThomPair y₀ θ₀) : Pair y₀ θ₀ stair = lamPos * lam2 := by
  unfold stair
  rw [map_sum]
  rw [Finset.sum_eq_single (0, 1)]
  · rw [map_smul, Pair_stairSimp H (by norm_num) (by norm_num) (by norm_num), ite_eq_left ⟨rfl, rfl⟩]
    norm_num
  · intro p hp hne
    simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨hs, ht⟩, hst⟩ := hp
    rw [map_smul, Pair_stairSimp H hs ht hst, ite_eq_right (by
      intro h; exact hne (Prod.ext h.1 h.2)), smul_zero]
  · intro h
    exfalso
    apply h
    simp [pairs]

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
