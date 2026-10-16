module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.FlatFan
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.FlatRho
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Flat.Loc

@[expose] public section


/-!
# The glued model of the flat

`FD` is the topological space obtained from six copies of the closed unit square (the squares of the chambers) by gluing the
`k`-th and `(k+1)`-st copies along their common wall (`t₁ = 1` for even `k`, `t₂ = 1` for odd `k`, indices mod `6`).  The chamber
maps descend to a continuous map `PiD : FD → Glued`, and the affine maps `hexLam k` descend to a continuous map `LamD : FD → ℝ²`.
The flat chain lifts to a chain `flatD` of `FD` whose boundary is the outer hexagon (the walls cancel in `FD` itself), whose image in
`Glued` is `flatChain`, and whose image in the plane under `LamD` is the straight fan `fanChain`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open TernaryPeriodPolynomials.Argument.Lemma33
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open CategoryTheory TernaryPoly TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.EquivariantSingularResolution SphereOddDegree
  SphereOddDegree.AffineBarycentricSubdivision

/-- The closed unit square. -/
abbrev SqT : Type := {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

/-- Six copies of the square. -/
abbrev DD : Type := Fin 6 × SqT

/-- The wall identifications: the squares `k` (even) and `k+1` along `t₁ = 1`, and `k` (odd) and `k+1 mod 6` along `t₂ = 1`. -/
def wallRel : DD → DD → Prop := fun x y =>
  ((x.1 = 0 ∨ x.1 = 2 ∨ x.1 = 4) ∧ y.1 = x.1 + 1 ∧ x.2.1.1 = 1 ∧ y.2.1.1 = 1 ∧ x.2.1.2 = y.2.1.2) ∨
  ((x.1 = 1 ∨ x.1 = 3 ∨ x.1 = 5) ∧ y.1 = x.1 + 1 ∧ x.2.1.2 = 1 ∧ y.2.1.2 = 1 ∧ x.2.1.1 = y.2.1.1)

/-- The glued flat. -/
abbrev FD : Type := Quot wallRel

/-- Clamping a point of the plane into the unit square. -/
def clampSq (p : ℝ × ℝ) : SqT :=
  ⟨(max 0 (min p.1 1), max 0 (min p.2 1)), by
    refine ⟨le_max_left _ _, ?_, le_max_left _ _, ?_⟩ <;> simp⟩

theorem continuous_clampSq : Continuous clampSq := by
  unfold clampSq
  exact Continuous.subtype_mk (by fun_prop) _

theorem clampSq_of_mem (p : ℝ × ℝ) (h : 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1) : (clampSq p).1 = p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  ext <;> simp [clampSq, h1, h2, h3, h4]

/-- The `k`-th chamber map into `FD`. -/
def fkD (k : ℕ) : C(ℝ × ℝ, TopCat.of FD) where
  toFun p := Quot.mk _ (Fin.ofNat 6 k, clampSq p)
  continuous_toFun := continuous_quot_mk.comp (continuous_const.prodMk continuous_clampSq)

theorem wall_chamber_even (k : ℕ) (hk : k = 0 ∨ k = 2 ∨ k = 4) (u : ℝ) :
    chamber (hexW k) (1, u) = chamber (hexW (k + 1)) (1, u) := by
  rw [hexW_succ_even k (by rcases hk with rfl | rfl | rfl <;> decide)]
  exact (chamber_wall_one _ _).symm

theorem wall_chamber_odd (k : ℕ) (hk : k = 1 ∨ k = 3 ∨ k = 5) (u : ℝ) :
    chamber (hexW k) (u, 1) = chamber (hexW (k + 1)) (u, 1) := by
  rw [hexW_succ_odd k (by rcases hk with rfl | rfl | rfl <;> decide)]
  exact (chamber_wall_two _ _).symm

/-- The chamber maps agree on glued points. -/
theorem wall_chamber (x y : DD) (h : wallRel x y) :
    chamber (hexW x.1.val) x.2.1 = chamber (hexW y.1.val) y.2.1 := by
  rcases h with ⟨hk, hy, h1, h2, h3⟩ | ⟨hk, hy, h1, h2, h3⟩
  · have hxe : x.2.1 = (1, x.2.1.2) := Prod.ext h1 rfl
    have hye : y.2.1 = (1, x.2.1.2) := Prod.ext h2 h3.symm
    rw [hxe, hye]
    rcases hk with h | h | h <;> rw [hy, h] <;> simp only [Fin.val_zero] <;>
      first
        | exact wall_chamber_even 0 (by decide) _
        | exact wall_chamber_even 2 (by decide) _
        | exact wall_chamber_even 4 (by decide) _
  · have hxe : x.2.1 = (x.2.1.1, 1) := Prod.ext rfl h1
    have hye : y.2.1 = (x.2.1.1, 1) := Prod.ext h3.symm h2
    rw [hxe, hye]
    rcases hk with h | h | h <;> rw [hy, h]
    · exact wall_chamber_odd 1 (by decide) _
    · exact wall_chamber_odd 3 (by decide) _
    · have e5 : chamber (hexW 5) (x.2.1.1, 1) = chamber (hexW (5 + 1)) (x.2.1.1, 1) := wall_chamber_odd 5 (by decide) _
      show chamber (hexW 5) (x.2.1.1, 1) = chamber (hexW 0) (x.2.1.1, 1)
      rw [← hexW_six]
      exact e5

theorem continuous_mk2 : Continuous (fun p : ℝ × ℝ => mk2 p.1 p.2) := by
  unfold mk2
  refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp ?_
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd

theorem continuous_hexLam (k : Fin 6) : Continuous (hexLam k) := by
  unfold hexLam
  have h : Continuous fun p : ℝ × ℝ => (hexM k 0 0 * (p.1 - 1) + hexM k 0 1 * (p.2 - 1),
      hexM k 1 0 * (p.1 - 1) + hexM k 1 1 * (p.2 - 1)) := by fun_prop
  exact continuous_mk2.comp h

/-- The glued chamber map. -/
def PiD : FD → Glued :=
  Quot.lift (fun x : DD => chamber (hexW x.1.val) x.2.1) (fun x y h => wall_chamber x y h)

theorem continuous_PiD : Continuous PiD := by
  apply continuous_quot_lift
  rw [continuous_prod_of_discrete_left]
  intro k
  exact (chamber (hexW k.val)).continuous.comp continuous_subtype_val

theorem PiD_mk (x : DD) : PiD (Quot.mk _ x) = chamber (hexW x.1.val) x.2.1 := rfl

/-- The glued affine map to the plane. -/
def LamD : FD → R2 :=
  Quot.lift (fun x : DD => hexLam x.1 x.2.1) (by
    intro x y h
    rcases h with ⟨hk, hy, h1, h2, h3⟩ | ⟨hk, hy, h1, h2, h3⟩
    · have hxe : x.2.1 = (1, x.2.1.2) := Prod.ext h1 rfl
      have hye : y.2.1 = (1, x.2.1.2) := Prod.ext h2 h3.symm
      rw [hxe, hye, hy]
      exact hexLam_wall_even _ hk _
    · have hxe : x.2.1 = (x.2.1.1, 1) := Prod.ext rfl h1
      have hye : y.2.1 = (x.2.1.1, 1) := Prod.ext h3.symm h2
      rw [hxe, hye, hy]
      exact hexLam_wall_odd _ hk _)

theorem continuous_LamD : Continuous LamD := by
  apply continuous_quot_lift
  rw [continuous_prod_of_discrete_left]
  intro k
  exact (continuous_hexLam k).comp continuous_subtype_val

theorem LamD_mk (x : DD) : LamD (Quot.mk _ x) = hexLam x.1 x.2.1 := rfl

/-- The glued flat as a bundled space. -/
abbrev FDT : TopCat.{0} := TopCat.of FD

/-- The glued chamber map as a morphism. -/
def PiHom : FDT ⟶ TopCat.of Glued := TopCat.ofHom ⟨PiD, continuous_PiD⟩

/-- The glued affine map as a morphism. -/
def LamHom : FDT ⟶ TopCat.of R2 := TopCat.ofHom ⟨LamD, continuous_LamD⟩

/-- The chain of a chamber square: two straight triangles. -/
def sqG {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) : singularChainGroup ℚ X 2 :=
  chainGenerator ℚ X 2 (tri f pv pa pO) + chainGenerator ℚ X 2 (tri f pv pO pb)

/-- The flat chain of `FD`: six chamber squares with alternating orientation. -/
def flatD : singularChainGroup ℚ FDT 2 :=
  sqG (fkD 0) - sqG (fkD 1) + sqG (fkD 2) - sqG (fkD 3) + sqG (fkD 4) - sqG (fkD 5)

/-- The closed unit square. -/
def sqSet : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1}

theorem convex_sqSet : Convex ℝ sqSet := by
  have : sqSet = Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext q; simp only [sqSet, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc]; tauto
  rw [this]; exact (convex_Icc 0 1).prod (convex_Icc 0 1)

theorem affSimplex_congr_sq {X : TopCat.{0}} (f g : C(ℝ × ℝ, X)) (hfg : ∀ q ∈ sqSet, f q = g q) {n : ℕ}
    (p : Fin (n + 1) → ℝ × ℝ) (hp : ∀ i, p i ∈ sqSet) : affSimplex f p = affSimplex g p := by
  unfold affSimplex
  congr 1
  apply ContinuousMap.ext
  intro x
  have hmem : affineMap n p x ∈ sqSet := by
    change ∑ i, x.weights i • p i ∈ sqSet
    exact convex_sqSet.sum_mem (fun i _ => x.weights_nonneg i) x.total_of_fintype (fun i _ => hp i)
  exact hfg _ hmem

theorem push_affSimplex {X Y : TopCat.{0}} (g : X ⟶ Y) (f : C(ℝ × ℝ, X)) {n : ℕ} (p : Fin (n + 1) → ℝ × ℝ) :
    pushSimplex g n (affSimplex f p) = affSimplex (g.hom.comp f) p := by
  change (Y.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n))).symm
      (singularSimplexAsContinuousMap Y n (pushSimplex g n (affSimplex f p))) = _
  rw [pushSimplex_continuousMap]
  simp [affSimplex, singularSimplexAsContinuousMap]

theorem hexLam_apply0 (k : Fin 6) (q : ℝ × ℝ) :
    hexLam k q 0 = hexM k 0 0 * (q.1 - 1) + hexM k 0 1 * (q.2 - 1) := by simp [hexLam, mk2]

theorem hexLam_apply1 (k : Fin 6) (q : ℝ × ℝ) :
    hexLam k q 1 = hexM k 1 0 * (q.1 - 1) + hexM k 1 1 * (q.2 - 1) := by simp [hexLam, mk2]

theorem affMapN_coord (n : ℕ) (w : Fin (n + 1) → R2) (t : Delta n) (j : Fin 2) :
    affMapN n w t j = ∑ i, t.weights i * w i j := by
  simp [affMapN]

theorem aff_comb (a b : ℝ) (n : ℕ) (t x y : Fin (n + 1) → ℝ) (hs : ∑ i, t i = 1) :
    a * (∑ i, t i * x i - 1) + b * (∑ i, t i * y i - 1) =
      ∑ i, t i * (a * (x i - 1) + b * (y i - 1)) := by
  have h1 : ∑ i, t i * (a * (x i - 1) + b * (y i - 1)) =
      a * ∑ i, t i * x i + b * ∑ i, t i * y i - (a + b) * ∑ i, t i := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [h1, hs]
  ring

theorem hexLam_affine (k : Fin 6) (n : ℕ) (p : Fin (n + 1) → ℝ × ℝ) (t : Delta n) :
    hexLam k (∑ i, t.weights i • p i) = affMapN n (fun i => hexLam k (p i)) t := by
  have hs : ∑ i, t.weights i = 1 := t.total_of_fintype
  ext j
  fin_cases j
  · rw [show ((fun i => i) ⟨0, by norm_num⟩ : Fin 2) = 0 from rfl, hexLam_apply0, affMapN_coord]
    simp only [hexLam_apply0, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exact aff_comb _ _ n _ _ _ hs
  · rw [show ((fun i => i) ⟨1, by norm_num⟩ : Fin 2) = 1 from rfl, hexLam_apply1, affMapN_coord]
    simp only [hexLam_apply1, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exact aff_comb _ _ n _ _ _ hs

theorem Fin_ofNat_val (k : Fin 6) : Fin.ofNat 6 k.val = k := Fin.ext (by simp)

theorem PiD_fkD (k : ℕ) (hk : k < 6) (q : ℝ × ℝ) (hq : q ∈ sqSet) : PiD (fkD k q) = fk k q := by
  change chamber (hexW (Fin.ofNat 6 k).val) (clampSq q).1 = chamber (hexW k) q
  rw [clampSq_of_mem q hq]
  simp [Nat.mod_eq_of_lt hk]

theorem LamD_fkD (k : Fin 6) (q : ℝ × ℝ) (hq : q ∈ sqSet) : LamD (fkD k.val q) = hexLam k q := by
  change hexLam (Fin.ofNat 6 k.val) (clampSq q).1 = hexLam k q
  rw [clampSq_of_mem q hq, Fin_ofNat_val]

theorem sq_pv : pv ∈ sqSet := by simp [sqSet, pv]
theorem sq_pa : pa ∈ sqSet := by simp [sqSet, pa]
theorem sq_pO : pO ∈ sqSet := by simp [sqSet, pO]
theorem sq_pb : pb ∈ sqSet := by simp [sqSet, pb]

theorem Pi_sqG (k : ℕ) (hk : k < 6) :
    (singularChainMap ℚ PiHom 2).hom (sqG (fkD k)) = sqG (fk k) := by
  have key : ∀ (p : Fin 3 → ℝ × ℝ), (∀ i, p i ∈ sqSet) →
      pushSimplex PiHom 2 (affSimplex (fkD k) p) = affSimplex (fk k) p := by
    intro p hp
    rw [push_affSimplex]
    exact affSimplex_congr_sq _ _ (fun q hq => PiD_fkD k hk q hq) p hp
  have hp : ∀ i, (![pv, pa, pO] : Fin 3 → ℝ × ℝ) i ∈ sqSet := by
    intro i; fin_cases i <;> first | exact sq_pv | exact sq_pa | exact sq_pO
  have hp' : ∀ i, (![pv, pO, pb] : Fin 3 → ℝ × ℝ) i ∈ sqSet := by
    intro i; fin_cases i <;> first | exact sq_pv | exact sq_pO | exact sq_pb
  unfold sqG tri
  rw [map_add, singularChainMap_generator, singularChainMap_generator, key _ hp, key _ hp']

theorem Pi_flatD : (singularChainMap ℚ PiHom 2).hom flatD = flatChain := by
  unfold flatD
  simp only [map_add, map_sub, Pi_sqG 0 (by norm_num), Pi_sqG 1 (by norm_num), Pi_sqG 2 (by norm_num),
    Pi_sqG 3 (by norm_num), Pi_sqG 4 (by norm_num), Pi_sqG 5 (by norm_num)]
  rfl

theorem affSimplex_Lam (k : Fin 6) (n : ℕ) (p : Fin (n + 1) → ℝ × ℝ) (hp : ∀ i, p i ∈ sqSet) :
    affSimplex (LamHom.hom.comp (fkD k.val)) p = affSimp n (fun i => hexLam k (p i)) := by
  unfold affSimplex affSimp continuousMapAsSingularSimplex
  congr 1
  apply ContinuousMap.ext
  intro t
  have hmem : affineMap n p t ∈ sqSet := by
    change ∑ i, t.weights i • p i ∈ sqSet
    exact convex_sqSet.sum_mem (fun i _ => t.weights_nonneg i) t.total_of_fintype (fun i _ => hp i)
  change LamD (fkD k.val (affineMap n p t)) = affMapN n (fun i => hexLam k (p i)) t
  rw [LamD_fkD k _ hmem]
  exact hexLam_affine k n p t

theorem Lam_sqG (k : Fin 6) :
    (singularChainMap ℚ LamHom 2).hom (sqG (fkD k.val)) =
      fanTri k (0, 0) (1, 0) (1, 1) + fanTri k (0, 0) (1, 1) (0, 1) := by
  have hp : ∀ i, (![pv, pa, pO] : Fin 3 → ℝ × ℝ) i ∈ sqSet := by
    intro i; fin_cases i <;> first | exact sq_pv | exact sq_pa | exact sq_pO
  have hp' : ∀ i, (![pv, pO, pb] : Fin 3 → ℝ × ℝ) i ∈ sqSet := by
    intro i; fin_cases i <;> first | exact sq_pv | exact sq_pO | exact sq_pb
  unfold sqG tri fanTri
  rw [map_add, singularChainMap_generator, singularChainMap_generator, push_affSimplex, push_affSimplex,
    affSimplex_Lam k 2 _ hp, affSimplex_Lam k 2 _ hp']
  congr 3 <;> (funext i; fin_cases i <;> rfl)

theorem Lam_flatD : (singularChainMap ℚ LamHom 2).hom flatD = fanChain := by
  have h0 : (singularChainMap ℚ LamHom 2).hom (sqG (fkD 0)) =
      fanTri 0 (0, 0) (1, 0) (1, 1) + fanTri 0 (0, 0) (1, 1) (0, 1) := Lam_sqG 0
  have h1 : (singularChainMap ℚ LamHom 2).hom (sqG (fkD 1)) =
      fanTri 1 (0, 0) (1, 0) (1, 1) + fanTri 1 (0, 0) (1, 1) (0, 1) := Lam_sqG 1
  have h2 : (singularChainMap ℚ LamHom 2).hom (sqG (fkD 2)) =
      fanTri 2 (0, 0) (1, 0) (1, 1) + fanTri 2 (0, 0) (1, 1) (0, 1) := Lam_sqG 2
  have h3 : (singularChainMap ℚ LamHom 2).hom (sqG (fkD 3)) =
      fanTri 3 (0, 0) (1, 0) (1, 1) + fanTri 3 (0, 0) (1, 1) (0, 1) := Lam_sqG 3
  have h4 : (singularChainMap ℚ LamHom 2).hom (sqG (fkD 4)) =
      fanTri 4 (0, 0) (1, 0) (1, 1) + fanTri 4 (0, 0) (1, 1) (0, 1) := Lam_sqG 4
  have h5 : (singularChainMap ℚ LamHom 2).hom (sqG (fkD 5)) =
      fanTri 5 (0, 0) (1, 0) (1, 1) + fanTri 5 (0, 0) (1, 1) (0, 1) := Lam_sqG 5
  unfold flatD fanChain
  simp only [map_add, map_sub, h0, h1, h2, h3, h4, h5, Fin.sum_univ_six]
  norm_num
  abel

/-- A segment as a chain of `singularChainGroup`. -/
def sg {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) (a b : ℝ × ℝ) : singularChainGroup ℚ X 1 :=
  chainGenerator ℚ X 1 (seg f a b)

theorem d_sqG {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) :
    (singularBoundary ℚ X 1).hom (sqG f) = sg f pv pa + sg f pa pO + sg f pO pb - sg f pv pb :=
  d_sqChain f

theorem ofNat_even (k : ℕ) (hk : k = 0 ∨ k = 2 ∨ k = 4) :
    (Fin.ofNat 6 k = 0 ∨ Fin.ofNat 6 k = 2 ∨ Fin.ofNat 6 k = 4) ∧
      Fin.ofNat 6 (k + 1) = Fin.ofNat 6 k + 1 := by
  rcases hk with rfl | rfl | rfl <;> decide

theorem ofNat_odd (k : ℕ) (hk : k = 1 ∨ k = 3 ∨ k = 5) :
    (Fin.ofNat 6 k = 1 ∨ Fin.ofNat 6 k = 3 ∨ Fin.ofNat 6 k = 5) ∧
      Fin.ofNat 6 (k + 1) = Fin.ofNat 6 k + 1 := by
  rcases hk with rfl | rfl | rfl <;> decide

theorem fkD_wall_one (k : ℕ) (hk : k = 0 ∨ k = 2 ∨ k = 4) (u : ℝ) :
    fkD (k + 1) (1, u) = fkD k (1, u) := by
  symm
  apply Quot.sound
  left
  refine ⟨(ofNat_even k hk).1, (ofNat_even k hk).2, ?_, ?_, rfl⟩
  · simp [clampSq]
  · simp [clampSq]

theorem fkD_wall_two (k : ℕ) (hk : k = 1 ∨ k = 3 ∨ k = 5) (u : ℝ) :
    fkD (k + 1) (u, 1) = fkD k (u, 1) := by
  symm
  apply Quot.sound
  right
  refine ⟨(ofNat_odd k hk).1, (ofNat_odd k hk).2, ?_, ?_, rfl⟩
  · simp [clampSq]
  · simp [clampSq]

theorem fkD_six : fkD 6 = fkD 0 := by
  ext q
  rfl

/-- The outer hexagon of the glued flat. -/
def hexBoundaryD : singularChainGroup ℚ FDT 1 :=
  (sg (fkD 0) pv pa - sg (fkD 0) pv pb) - (sg (fkD 1) pv pa - sg (fkD 1) pv pb) +
    (sg (fkD 2) pv pa - sg (fkD 2) pv pb) - (sg (fkD 3) pv pa - sg (fkD 3) pv pb) +
    (sg (fkD 4) pv pa - sg (fkD 4) pv pb) - (sg (fkD 5) pv pa - sg (fkD 5) pv pb)

/-- **The walls cancel in `FD`: the boundary of the flat is the outer hexagon.** -/
theorem d_flatD : (singularBoundary ℚ FDT 1).hom flatD = hexBoundaryD := by
  have e0 : sg (fkD 1) pa pO = sg (fkD 0) pa pO := by
    unfold sg; rw [seg_wall_one (fkD 1) (fkD 0) (fkD_wall_one 0 (by decide))]
  have e2 : sg (fkD 3) pa pO = sg (fkD 2) pa pO := by
    unfold sg; rw [seg_wall_one (fkD 3) (fkD 2) (fkD_wall_one 2 (by decide))]
  have e4 : sg (fkD 5) pa pO = sg (fkD 4) pa pO := by
    unfold sg; rw [seg_wall_one (fkD 5) (fkD 4) (fkD_wall_one 4 (by decide))]
  have e1 : sg (fkD 2) pO pb = sg (fkD 1) pO pb := by
    unfold sg; rw [seg_wall_two (fkD 2) (fkD 1) (fkD_wall_two 1 (by decide))]
  have e3 : sg (fkD 4) pO pb = sg (fkD 3) pO pb := by
    unfold sg; rw [seg_wall_two (fkD 4) (fkD 3) (fkD_wall_two 3 (by decide))]
  have e5 : sg (fkD 0) pO pb = sg (fkD 5) pO pb := by
    unfold sg; rw [← fkD_six, seg_wall_two (fkD 6) (fkD 5) (fkD_wall_two 5 (by decide))]
  unfold flatD hexBoundaryD
  simp only [map_add, map_sub, d_sqG]
  rw [e0, e2, e4, e1, e3, e5]
  abel

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
