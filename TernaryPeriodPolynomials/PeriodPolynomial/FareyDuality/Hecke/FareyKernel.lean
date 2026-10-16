module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.Hecke.DualBoundary

@[expose] public section


/-!
# The kernel of the symbol map

Formalized by Claude Sonnet 5.5.

**Exactness of the Steinberg presentation.**  For an antisymmetric chain `x` of oriented dual edges with `piT x = 0`
there is a chain `w` of triangles with `bdryMap w = x` (`exists_bdry_preimage`).  This is the library's filling theorem
`RankTwoHeightOne.ambient_one_cycle_filling` (every finite one-cycle of the Farey complex bounds) transported through
the dictionary

* `Th1 : ℚ[OTE] → Ch`, `theta1 q = det γ · [γ cusp₁, γ cusp₂]` (`q = γ • p0`), `∂ Th1 = ι ∘ piT`,
* `Th2 : ℚ[Tri] → Ch`, `theta2 t` the cone over the boundary cycle `zTri t` of `t` (canonical, with
  `theta2 (g • triPlus) = det g · [g cusp₁, g cusp₂, g cusp₃]`), `∂ Th2 = zTri` and `Th1 ∘ bdryMap = -2 ∂ Th2`,
* `Th1_injective_anti` (`EdgeChainInjective`), and `chains3_le_range`: every triangle chain of the Farey complex is
  `Th2` of a chain of triangles (`simplex3_perm`: any ordering of the vertices of a triangle is `±` the standard one).

Hence `St^δ = ℚ[OTE]^{anti} / bdryMap (ℚ[Tri])`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeDuality

open CategoryTheory TernaryPoly TernaryPoly.BinaryModularSymbol TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.FareyTree
open scoped MonoidAlgebra Classical

abbrev Ch := OrientedListChains.Chain Line

section ListLemmas

variable {V : Type*} (a b c : V)

theorem s_bac : OrientedListChains.simplex [b, a, c] = - OrientedListChains.simplex [a, b, c] :=
  OrientedListChains.simplex_swap_eq_neg b a [c]

theorem s_acb : OrientedListChains.simplex [a, c, b] = - OrientedListChains.simplex [a, b, c] := by
  rw [← OrientedListChains.cons_simplex, OrientedListChains.simplex_swap_eq_neg c b [], map_neg,
    OrientedListChains.cons_simplex]

theorem s_bca : OrientedListChains.simplex [b, c, a] = OrientedListChains.simplex [a, b, c] := by
  rw [← OrientedListChains.cons_simplex, OrientedListChains.simplex_swap_eq_neg c a [], map_neg,
    OrientedListChains.cons_simplex, s_bac a b c, neg_neg]

theorem s_cab : OrientedListChains.simplex [c, a, b] = OrientedListChains.simplex [a, b, c] := by
  rw [OrientedListChains.simplex_swap_eq_neg c a [b], s_acb a b c, neg_neg]

theorem s_cba : OrientedListChains.simplex [c, b, a] = - OrientedListChains.simplex [a, b, c] := by
  rw [OrientedListChains.simplex_swap_eq_neg c b [a], s_bca a b c]

theorem s_cac : OrientedListChains.simplex [a, c, a] = 0 := by
  have := OrientedListChains.simplex_repeat a [c] []
  simpa using this

theorem s_aab : OrientedListChains.simplex [a, a, b] = 0 :=
  OrientedListChains.simplex_repeat_adjacent a [b]

/-- The boundary of a triangle. -/
theorem boundary_simplex3 (V' : Type*) (x y z : V') :
    OrientedListChains.boundary (OrientedListChains.simplex [x, y, z]) =
      OrientedListChains.simplex [x, y] + OrientedListChains.simplex [y, z] +
        OrientedListChains.simplex [z, x] := by
  have h1 : OrientedListChains.simplex [z, x] = - OrientedListChains.simplex [x, z] :=
    OrientedListChains.simplex_swap_eq_neg z x []
  rw [h1]
  simp only [OrientedListChains.boundary_cons, OrientedListChains.boundary_nil, map_zero, sub_zero,
    OrientedListChains.cons_simplex, map_sub]
  abel

/-- Coning the boundary cycle of a triangle from its three vertices. -/
theorem cone_sum (x y z : V) :
    OrientedListChains.cons x (OrientedListChains.simplex [x, y] + OrientedListChains.simplex [y, z] +
        OrientedListChains.simplex [z, x]) +
      OrientedListChains.cons y (OrientedListChains.simplex [x, y] + OrientedListChains.simplex [y, z] +
        OrientedListChains.simplex [z, x]) +
      OrientedListChains.cons z (OrientedListChains.simplex [x, y] + OrientedListChains.simplex [y, z] +
        OrientedListChains.simplex [z, x]) = (3 : ℚ) • OrientedListChains.simplex [x, y, z] := by
  simp only [map_add, OrientedListChains.cons_simplex]
  have e1 : OrientedListChains.simplex [y, x, y] = 0 := s_cac y x
  have e2 : OrientedListChains.simplex [y, y, z] = 0 := s_aab y z
  have e3 : OrientedListChains.simplex [z, y, z] = 0 := s_cac z y
  have e4 : OrientedListChains.simplex [z, z, x] = 0 := s_aab z x
  have e5 : OrientedListChains.simplex [x, z, x] = 0 := s_cac x z
  have e6 : OrientedListChains.simplex [x, x, y] = 0 := s_aab x y
  rw [e1, e2, e3, e4, e5, e6, s_bca x y z, s_cab x y z]
  module

end ListLemmas

theorem boundary_chD (g : IntegralGL) (c : Ch) :
    OrientedListChains.boundary (chD g c) = chD g (OrientedListChains.boundary c) := by
  rw [chD_apply, chD_apply, map_smul, boundary_chAct]

theorem chD_cons (g : IntegralGL) (a : Line) (c : Ch) :
    chD g (OrientedListChains.cons a c) = OrientedListChains.cons (g • a) (chD g c) := by
  rw [chD_apply, chD_apply, chAct_cons, map_smul]

/-- The boundary cycle of the standard triangle. -/
def Z0 : Ch :=
  OrientedListChains.simplex [cusp1, cusp2] + OrientedListChains.simplex [cusp2, cusp3] +
    OrientedListChains.simplex [cusp3, cusp1]

theorem chD_rho_sig1 : chD rho sig1 = OrientedListChains.simplex [cusp2, cusp3] := by
  rw [chD_apply, sig1, chAct_simplex]
  simp only [List.map_cons, List.map_nil, rho_c1, rho_c2, detQ_rho, one_smul]

theorem chD_rho2_sig1 : chD rho2 sig1 = OrientedListChains.simplex [cusp3, cusp1] := by
  rw [chD_apply, sig1, chAct_simplex]
  simp only [List.map_cons, List.map_nil, rho2_c1, rho2_c2, detQ_rho2, one_smul]

theorem Z0_eq : sig1 + chD rho sig1 + chD rho2 sig1 = Z0 := by
  rw [chD_rho_sig1, chD_rho2_sig1, Z0, sig1]

/-- The sum of the edge chains of the oriented edges leaving a triangle. -/
def zTri (t : Tri) : Ch := ∑ q ∈ nbF t, theta1 q

theorem zTri_gtri (g : IntegralGL) : zTri (g • triPlus) = chD g Z0 := by
  unfold zTri
  rw [sum_nbF, theta1_apply, theta1_apply, theta1_apply, ← Z0_eq, map_mul, map_mul]
  simp only [map_add]
  rfl

/-- The standard oriented triangle. -/
def sig2 : Ch := OrientedListChains.simplex [cusp1, cusp2, cusp3]

theorem boundary_sig2 : OrientedListChains.boundary sig2 = Z0 := boundary_simplex3 Line _ _ _

/-- The oriented triangle chain of a triangle, as the cone over its boundary cycle. -/
def theta2 (t : Tri) : Ch :=
  (1 / 3 : ℚ) • ∑ x ∈ t.1, OrientedListChains.cons x (zTri t)

theorem theta2_gtri (g : IntegralGL) : theta2 (g • triPlus) = chD g sig2 := by
  unfold theta2
  rw [tri_smul_val, Finset.sum_image (fun a _ b _ h => MulAction.injective g h), zTri_gtri]
  have h12 : cusp1 ≠ cusp2 := cusp1_ne_cusp2
  have h13 : cusp1 ≠ cusp3 := cusp3_ne_cusp1.symm
  have h23 : cusp2 ≠ cusp3 := cusp3_ne_cusp2.symm
  have hs : ∑ x ∈ triPlus.1, OrientedListChains.cons (g • x) (chD g Z0) =
      chD g (∑ x ∈ triPlus.1, OrientedListChains.cons x Z0) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun x _ => (chD_cons g x Z0).symm
  rw [hs]
  have : ∑ x ∈ triPlus.1, OrientedListChains.cons x Z0 = (3 : ℚ) • sig2 := by
    have : triPlus.1 = {cusp1, cusp2, cusp3} := rfl
    rw [this, Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton, sig2, Z0, ← cone_sum cusp1 cusp2 cusp3]
    abel
  rw [this, map_smul, smul_smul]
  norm_num

theorem boundary_theta2 (t : Tri) : OrientedListChains.boundary (theta2 t) = zTri t := by
  obtain ⟨g, rfl⟩ := exists_smul_triPlus t
  rw [theta2_gtri, boundary_chD, boundary_sig2, zTri_gtri]


theorem Th1_bdryV (t : Tri) : Th1 (bdryV t) = (-2 : ℚ) • zTri t := by
  unfold bdryV zTri
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_sub, Th1_single, Th1_single, theta1_swap]
  module

/-- The triangle chain map on the permutation module of triangles. -/
def Th2 : MonoidAlgebra ℚ Tri →ₗ[ℚ] Ch :=
  Finsupp.linearCombination ℚ theta2 ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem Th2_single (t : Tri) (r : ℚ) : Th2 (MonoidAlgebra.single t r) = r • theta2 t := by
  simp [Th2]

theorem Th1_bdryMap (w : P0) :
    Th1 (bdryMap.hom w) = (-2 : ℚ) • OrientedListChains.boundary (Th2 w) := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb, smul_add]
  | single t r =>
    rw [bdryMap_single, map_smul, Th1_bdryV, Th2_single, map_smul, boundary_theta2]
    module

theorem edge_allowed (γ : IntegralGL) : OrientedListChains.Allowed ambient [γ • cusp1, γ • cusp2] := by
  right
  refine ⟨⟨γ • cusp1, by simp⟩, γ, ?_⟩
  intro x hx
  simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, (smul_cusp1 γ).symm⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, (smul_cusp2 γ).symm⟩

theorem theta1_mem_chains (q : OTE) : theta1 q ∈ OrientedListChains.chains ambient 2 := by
  obtain ⟨γ, rfl⟩ := ote_transitive q
  rw [theta1_apply, chD_apply, sig1, chAct_simplex]
  refine Submodule.smul_mem _ _ ?_
  exact OrientedListChains.simplex_mem_chains ambient [γ • cusp1, γ • cusp2] (edge_allowed γ)

theorem Th1_mem_chains (c : PE) : Th1 c ∈ OrientedListChains.chains ambient 2 := by
  rw [Th1_apply]
  exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (theta1_mem_chains q)


theorem simplex3_perm {V : Type*} {a b c x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x = a ∨ x = b ∨ x = c) (hy : y = a ∨ y = b ∨ y = c) (hz : z = a ∨ z = b ∨ z = c) :
    ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧
      OrientedListChains.simplex [x, y, z] = ε • OrientedListChains.simplex [a, b, c] := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
    first
    | exact (hxy rfl).elim
    | exact (hxz rfl).elim
    | exact (hyz rfl).elim
    | exact ⟨1, Or.inl rfl, (one_smul _ _).symm⟩
    | exact ⟨-1, Or.inr rfl, by rw [neg_one_smul]; first | exact s_acb _ _ _ | exact s_bac _ _ _ | exact s_cba _ _ _⟩
    | exact ⟨1, Or.inl rfl, by rw [one_smul]; first | exact s_bca _ _ _ | exact s_cab _ _ _⟩

theorem simplex_mem_range_Th2 (l : List Line) (hlen : l.length = 3)
    (hl : OrientedListChains.Allowed ambient l) :
    OrientedListChains.simplex l ∈ LinearMap.range Th2 := by
  obtain ⟨x, y, z, rfl⟩ := List.length_eq_three.mp hlen
  by_cases hnd : [x, y, z].Nodup
  · have hxy : x ≠ y := fun h => by subst h; simp at hnd
    have hxz : x ≠ z := fun h => by subst h; simp at hnd
    have hyz : y ≠ z := fun h => by subst h; simp at hnd
    have hface := hl.resolve_left (by simp)
    obtain ⟨_, g, hsub⟩ := hface
    have hsub' : ({x, y, z} : Finset Line) ⊆ augmentedFrame g := by
      intro u hu
      have h2 : u ∈ [x, y, z] := by simpa using hu
      exact hsub ((@List.mem_toFinset _ (fun a b => Classical.propDecidable (a = b)) _ _).mpr h2)
    have hcard : ({x, y, z} : Finset Line).card = 3 := Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
    have hEq : ({x, y, z} : Finset Line) = augmentedFrame g :=
      Finset.eq_of_subset_of_card_le hsub' (by rw [hcard, frame_card])
    let t : Tri := ⟨augmentedFrame g, g, rfl⟩
    obtain ⟨γ, hγ⟩ := exists_smul_triPlus t
    have hmem : ∀ u : Line, u ∈ ({x, y, z} : Finset Line) →
        u = γ • cusp1 ∨ u = γ • cusp2 ∨ u = γ • cusp3 := by
      intro u hu
      rw [hEq] at hu
      have hu' : u ∈ (γ • triPlus).1 := by rw [← hγ]; exact hu
      rw [tri_smul_val, Finset.mem_image] at hu'
      obtain ⟨v, hv, rfl⟩ := hu'
      rw [mem_triPlus_cusps] at hv
      rcases hv with rfl | rfl | rfl <;> simp
    obtain ⟨ε, hε, hperm⟩ := simplex3_perm (a := γ • cusp1) (b := γ • cusp2) (c := γ • cusp3)
      hxy hxz hyz (hmem x (by simp)) (hmem y (by simp)) (hmem z (by simp))
    refine ⟨MonoidAlgebra.single t (ε * detQ γ), ?_⟩
    rw [Th2_single, hγ, theta2_gtri, chD_apply, sig2, chAct_simplex, hperm]
    simp only [List.map_cons, List.map_nil]
    rw [smul_smul, mul_assoc, detQ_mul_self, mul_one]
  · rw [OrientedListChains.simplex_eq_zero_of_not_nodup _ hnd]
    exact Submodule.zero_mem _


theorem chains3_le_range {b : Ch} (hb : b ∈ OrientedListChains.chains ambient 3) :
    b ∈ LinearMap.range Th2 := by
  have : OrientedListChains.chains ambient 3 ≤ LinearMap.range Th2 := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hlen, hl, rfl⟩
    exact simplex_mem_range_Th2 l hlen hl
  exact this hb

/-- **The kernel of the symbol map on antisymmetric chains is the image of the dual boundary.** -/
theorem exists_bdry_preimage (x : PE) (hx : x ∈ antiSub) (hπ : piT.hom x = 0) :
    ∃ w : P0, bdryMap.hom w = x := by
  have hcyc : OrientedListChains.boundary (Th1 x) = 0 := by
    rw [boundary_Th1, hπ]; simp
  obtain ⟨b, hb, hdb⟩ :=
    TernaryPoly.RankTwoHeightOne.ambient_one_cycle_filling (Th1_mem_chains x) hcyc
  obtain ⟨w, hw⟩ := chains3_le_range hb
  refine ⟨(-1 / 2 : ℚ) • w, ?_⟩
  have hy : Th1 (x + (1 / 2 : ℚ) • bdryMap.hom w) = 0 := by
    rw [map_add, map_smul, Th1_bdryMap, hw, hdb]
    module
  have hanti : x + (1 / 2 : ℚ) • bdryMap.hom w ∈ antiSub :=
    antiSub.add_mem hx (antiSub.smul_mem _ (bdryMap_mem_antiSub w))
  have h0 := Th1_injective_anti hanti hy
  have h2 : x = -((1 / 2 : ℚ) • bdryMap.hom w) := eq_neg_of_add_eq_zero_left h0
  rw [map_smul, h2]
  module

end TernaryPeriodPolynomials.Argument.HeckeDuality
