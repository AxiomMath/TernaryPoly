module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Orient.Linearize
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Orient.GLPath

@[expose] public section


/-!
# Local degree of affine tetrahedra around the origin

* `degSimplex`, `degSimplex_homotopy`: the local degree `H₃(ℝ³, ℝ³∖0) ≅ ℚ` of a singular 3-simplex
  `f : Δ³ → ℝ³` whose boundary avoids the origin, invariant under homotopies of simplices whose
  boundaries avoid the origin (the pair `(Δ³, ∂Δ³)`, from `relCls_homotopy`).
* `degAff w`, `degAff_homotopy`: the same for the affine simplex with vertices `w : Fin 4 → ℝ³`
  and paths of vertex tuples.
* `lamPos`: the local degree of the reference tetrahedron `rv = (e₂, e₁, e₃, -(e₁+e₂+e₃))`
  (centroid at the origin, `edgeDet > 0`).
* `degAff_universal`: **every** tetrahedron `w` with `edgeDet w > 0` and a positive relation
  `∑ τₖ wₖ = 0` (the origin in its interior) has `degAff w = lamPos`.  Proof: positive rescaling of the
  vertices (`degAff_rref`), the linear map `Amat` carrying the weighted reference onto `w` has positive
  determinant, and it is joined to the identity by a path of invertible matrices
  (`GLPath.conn_of_det_pos`; `degAff_mulE`).  The local degree is thus the same universal rational
  number `lamPos` for all positively oriented tetrahedra around the origin; reflections are never
  needed.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical
open TernaryPoly TernaryPoly.SymmetricSpacePositive
  CategoryTheory Limits HomologicalComplex TernaryPoly.RationalSingularAugmentation
  TernaryPoly.RationalRelativeSingular TernaryPoly.ContractibleSingularHomology
  TernaryPoly.FreeActionLinearization TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalSphere
  TernaryPeriodPolynomials.Argument.Lemma33

namespace TernaryPeriodPolynomials.Argument.Lemma33.Orient

/-! ### The standard simplex as a pair -/

/-- The standard 3-simplex. -/
abbrev Dl := Convexity.StdSimplex ℝ (Fin (3 + 1))

/-- Its boundary. -/
def bdry : Set Dl := {t | ∃ i, t.weights i = 0}

/-- The identity singular simplex. -/
def idSimplex : SingularSimplex (TopCat.of Dl) 3 :=
  ((TopCat.of Dl).toSSetObjEquiv _).symm (ContinuousMap.id Dl)

theorem idSimplex_relCycle : RelCycle bdry (sing (TopCat.of Dl) idSimplex) := by
  apply relCycle_of_mem_range
  rw [d_sing]
  refine Submodule.sum_mem _ (fun i _ => Submodule.smul_of_tower_mem _ _ ?_)
  apply sing_mem_range
  intro t
  refine ⟨i, ?_⟩
  rw [TopCat.toSSetObjEquiv_δ_apply]
  simp only [idSimplex, Equiv.apply_symm_apply]
  change (Convexity.StdSimplex.map i.succAbove t).weights i = 0
  rw [SphereOddDegree.AffineBarycentricSubdivision.weights_map_apply]
  apply Finset.sum_eq_zero
  intro k hk
  exact absurd (Finset.mem_filter.mp hk).2 (Fin.succAbove_ne i k)


/-- The singular 3-simplex of Euclidean space given by a continuous map on the standard simplex. -/
def simpOf (f : C(Dl, E3)) : SingularSimplex (TopCat.of E3) 3 :=
  ((TopCat.of E3).toSSetObjEquiv _).symm f

theorem chainMap_idSimplex (f : C(Dl, E3)) :
    AbF.map ((chainMap f).f 3) (sing (TopCat.of Dl) idSimplex) = sing (TopCat.of E3) (simpOf f) := by
  change ((chainMap f).f 3).hom (sing (TopCat.of Dl) idSimplex) = _
  rw [chainMap_sing]
  congr 1

theorem simplex_relCycle (f : C(Dl, E3)) (hf : ∀ t ∈ bdry, f t ≠ 0) :
    RelCycle (Punctured 3) (sing (TopCat.of E3) (simpOf f)) := by
  rw [← chainMap_idSimplex]
  exact RelCycle.map f bdry (Punctured 3) (fun t ht h0 => hf t ht h0) _ idSimplex_relCycle

/-- The local degree of a singular simplex whose boundary avoids the origin. -/
def degSimplex (f : C(Dl, E3)) (hf : ∀ t ∈ bdry, f t ≠ 0) : ℚ :=
  degRel (sing (TopCat.of E3) (simpOf f)) (simplex_relCycle f hf)

theorem degSimplex_homotopy (f g : C(Dl, E3)) (hf : ∀ t ∈ bdry, f t ≠ 0)
    (hg : ∀ t ∈ bdry, g t ≠ 0) (H : ContinuousMap.Homotopy f g)
    (hH : ∀ s t, t ∈ bdry → H (s, t) ≠ 0) : degSimplex f hf = degSimplex g hg := by
  unfold degSimplex degRel
  congr 1
  have hh := relCls_homotopy f g bdry (Punctured 3) (fun t ht h0 => hf t ht h0)
    (fun t ht h0 => hg t ht h0) H (fun s t ht h0 => hH s t ht h0)
    (sing (TopCat.of Dl) idSimplex) idSimplex_relCycle
    (RelCycle.map f bdry (Punctured 3) (fun t ht h0 => hf t ht h0) _ idSimplex_relCycle)
    (RelCycle.map g bdry (Punctured 3) (fun t ht h0 => hg t ht h0) _ idSimplex_relCycle)
  calc relCls (Punctured 3) (sing (TopCat.of E3) (simpOf f)) (simplex_relCycle f hf)
      = relCls (Punctured 3) (AbF.map ((chainMap f).f 3) (sing (TopCat.of Dl) idSimplex))
          (RelCycle.map f bdry (Punctured 3) (fun t ht h0 => hf t ht h0) _ idSimplex_relCycle) :=
        relCls_congr _ _ _ _ _ (chainMap_idSimplex f).symm
    _ = relCls (Punctured 3) (AbF.map ((chainMap g).f 3) (sing (TopCat.of Dl) idSimplex))
          (RelCycle.map g bdry (Punctured 3) (fun t ht h0 => hg t ht h0) _ idSimplex_relCycle) := hh
    _ = relCls (Punctured 3) (sing (TopCat.of E3) (simpOf g)) (simplex_relCycle g hg) :=
        relCls_congr _ _ _ _ _ (chainMap_idSimplex g)


/-! ### Affine simplices of Euclidean space -/

/-- The affine map from the standard simplex onto the simplex with vertices `w`. -/
def affEMap (w : Fin (3 + 1) → E3) : C(Dl, E3) where
  toFun t := ∑ k, t.weights k • w k
  continuous_toFun := by
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact (Convexity.StdSimplex.continuous_weights_apply ℝ i).smul continuous_const

/-- No point of the boundary of the simplex is the origin. -/
def FacesAvoid (w : Fin (3 + 1) → E3) : Prop := ∀ t ∈ bdry, affEMap w t ≠ 0

/-- The local degree of the affine simplex `w`, when its faces avoid the origin. -/
def degAff (w : Fin (3 + 1) → E3) (h : FacesAvoid w) : ℚ := degSimplex (affEMap w) h

theorem degAff_congr (w w' : Fin (3 + 1) → E3) (h : FacesAvoid w) (h' : FacesAvoid w') (e : w = w') :
    degAff w h = degAff w' h' := by
  subst e; rfl

/-- Homotopy invariance for paths of affine simplices whose faces avoid the origin. -/
theorem degAff_homotopy (w w' : Fin (3 + 1) → E3) (h : FacesAvoid w) (h' : FacesAvoid w')
    (W : unitInterval → Fin (3 + 1) → E3) (hW : ∀ k, Continuous fun s => W s k)
    (h0 : W 0 = w) (h1 : W 1 = w') (hf : ∀ s, FacesAvoid (W s)) : degAff w h = degAff w' h' := by
  unfold degAff
  refine degSimplex_homotopy (affEMap w) (affEMap w') h h' ?_ ?_
  · exact
      { toFun := fun p => affEMap (W p.1) p.2
        continuous_toFun := by
          change Continuous fun p : unitInterval × Dl => ∑ k, p.2.weights k • W p.1 k
          refine continuous_finsetSum _ (fun k _ => ?_)
          exact ((Convexity.StdSimplex.continuous_weights_apply ℝ k).comp continuous_snd).smul
            ((hW k).comp continuous_fst)
        map_zero_left := fun t => by simp [h0]
        map_one_left := fun t => by simp [h1] }
  · intro s t ht
    exact hf s t ht


/-! ### The reference tetrahedron -/

/-- The vector with the given coordinates. -/
def mk3 (a b c : ℝ) : E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![a, b, c]

@[simp] theorem mk3_zero (a b c : ℝ) : mk3 a b c 0 = a := rfl
@[simp] theorem mk3_one (a b c : ℝ) : mk3 a b c 1 = b := rfl
@[simp] theorem mk3_two (a b c : ℝ) : mk3 a b c 2 = c := rfl

/-- The vertices of the reference tetrahedron `(e₂, e₁, e₃, -(e₁+e₂+e₃))`, positively oriented and
with centroid at the origin. -/
def rv : Fin (3 + 1) → E3 := ![mk3 0 1 0, mk3 1 0 0, mk3 0 0 1, mk3 (-1) (-1) (-1)]

/-- The reference tetrahedron with its vertices scaled by positive factors `c`. -/
def rref (c : Fin (3 + 1) → ℝ) : Fin (3 + 1) → E3 := fun k => c k • rv k

theorem rref_apply (c : Fin (3 + 1) → ℝ) (t : Dl) (i : Fin 3) :
    affEMap (rref c) t i = match i with
      | 0 => t.weights 1 * c 1 - t.weights 3 * c 3
      | 1 => t.weights 0 * c 0 - t.weights 3 * c 3
      | 2 => t.weights 2 * c 2 - t.weights 3 * c 3 := by
  fin_cases i <;>
    simp [affEMap, rref, rv, Fin.sum_univ_succ, mk3] <;> ring

theorem rref_facesAvoid (c : Fin (3 + 1) → ℝ) (hc : ∀ k, 0 < c k) : FacesAvoid (rref c) := by
  intro t ht h0
  obtain ⟨i, hi⟩ := ht
  have e0 := congrArg (fun v : E3 => v 0) h0
  have e1 := congrArg (fun v : E3 => v 1) h0
  have e2 := congrArg (fun v : E3 => v 2) h0
  simp only [rref_apply, PiLp.zero_apply] at e0 e1 e2
  have hs : t.weights 0 + t.weights 1 + t.weights 2 + t.weights 3 = 1 := by
    have h4 : ∑ k, t.weights k = 1 := t.total_of_fintype
    rw [Fin.sum_univ_four] at h4
    exact h4
  have hn : ∀ k, 0 ≤ t.weights k := t.weights_nonneg
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  have c3 := hc 3
  have n0 := hn 0
  have n1 := hn 1
  have n2 := hn 2
  have n3 := hn 3
  fin_cases i <;> simp at hi
  · have : t.weights 0 * c 0 = 0 := by rw [hi]; ring
    have h3 : t.weights 3 * c 3 = 0 := by linarith
    have h1 : t.weights 1 * c 1 = 0 := by linarith
    have h2 : t.weights 2 * c 2 = 0 := by linarith
    have a1 : t.weights 1 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h c1.ne'
    have a2 : t.weights 2 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h c2.ne'
    have a3 : t.weights 3 = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h c3.ne'
    linarith
  · have : t.weights 1 * c 1 = 0 := by rw [hi]; ring
    have h3 : t.weights 3 * c 3 = 0 := by linarith
    have h0' : t.weights 0 * c 0 = 0 := by linarith
    have h2 : t.weights 2 * c 2 = 0 := by linarith
    have a0 : t.weights 0 = 0 := by
      rcases mul_eq_zero.mp h0' with h | h
      · exact h
      · exact absurd h c0.ne'
    have a2 : t.weights 2 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h c2.ne'
    have a3 : t.weights 3 = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h c3.ne'
    linarith
  · have : t.weights 2 * c 2 = 0 := by rw [hi]; ring
    have h3 : t.weights 3 * c 3 = 0 := by linarith
    have h0' : t.weights 0 * c 0 = 0 := by linarith
    have h1 : t.weights 1 * c 1 = 0 := by linarith
    have a0 : t.weights 0 = 0 := by
      rcases mul_eq_zero.mp h0' with h | h
      · exact h
      · exact absurd h c0.ne'
    have a1 : t.weights 1 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h c1.ne'
    have a3 : t.weights 3 = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h c3.ne'
    linarith
  · have : t.weights 3 * c 3 = 0 := by rw [hi]; ring
    have h0' : t.weights 0 * c 0 = 0 := by linarith
    have h1 : t.weights 1 * c 1 = 0 := by linarith
    have h2 : t.weights 2 * c 2 = 0 := by linarith
    have a0 : t.weights 0 = 0 := by
      rcases mul_eq_zero.mp h0' with h | h
      · exact h
      · exact absurd h c0.ne'
    have a1 : t.weights 1 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h c1.ne'
    have a2 : t.weights 2 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h c2.ne'
    linarith


/-- **The universal local class of a positively oriented tetrahedron around the origin**
(the class of the reference tetrahedron `rv`). -/
def lamPos : ℚ := degAff (rref 1) (rref_facesAvoid 1 (fun _ => one_pos))

theorem degAff_rref (c : Fin (3 + 1) → ℝ) (hc : ∀ k, 0 < c k) :
    degAff (rref c) (rref_facesAvoid c hc) = lamPos := by
  unfold lamPos
  refine (degAff_homotopy (rref 1) (rref c) _ _
    (fun s => rref (fun k => (1 - (s : ℝ)) + (s : ℝ) * c k)) ?_ ?_ ?_ ?_).symm
  · intro k
    simp only [rref]
    exact ((continuous_const.sub continuous_subtype_val).add
      (continuous_subtype_val.mul continuous_const)).smul continuous_const
  · funext k; simp [rref]
  · funext k; simp [rref]
  · intro s
    apply rref_facesAvoid
    intro k
    have h1 := s.2.1
    have h2 := s.2.2
    have h3 := hc k
    have hm := lt_min one_pos h3
    have a : min 1 (c k) ≤ 1 := min_le_left _ _
    have b : min 1 (c k) ≤ c k := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_left a (sub_nonneg.2 h2), mul_le_mul_of_nonneg_left b h1]


/-! ### Linear maps and path-connected families of linear maps -/

/-- The action of a real `3 × 3` matrix on Euclidean space. -/
def mulE (A : Matrix (Fin 3) (Fin 3) ℝ) (x : E3) : E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (A.mulVec (EuclideanSpace.equiv (Fin 3) ℝ x))

theorem mulE_one (x : E3) : mulE 1 x = x := by
  simp [mulE]

theorem mulE_sum {ι : Type} (A : Matrix (Fin 3) (Fin 3) ℝ) (s : Finset ι) (c : ι → ℝ)
    (v : ι → E3) : mulE A (∑ k ∈ s, c k • v k) = ∑ k ∈ s, c k • mulE A (v k) := by
  have : mulE A = ⇑((EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearMap ∘ₗ
      (Matrix.mulVecLin A) ∘ₗ (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap) := by
    ext x; rfl
  rw [this]
  simp [map_sum, map_smul]

theorem mulE_eq_zero {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.det ≠ 0) {x : E3} (h : mulE A x = 0) :
    x = 0 := by
  have h1 : A.mulVec (EuclideanSpace.equiv (Fin 3) ℝ x) = 0 := by
    have := congrArg (EuclideanSpace.equiv (Fin 3) ℝ) h
    simpa [mulE] using this
  have h2 := Matrix.eq_zero_of_mulVec_eq_zero hA h1
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  simpa using h2

theorem continuous_mulE {T : Type} [TopologicalSpace T] {f : T → Matrix (Fin 3) (Fin 3) ℝ} {g : T → E3}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun p => mulE (f p) (g p) := by
  unfold mulE
  refine (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp ?_
  exact hf.matrix_mulVec ((EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp hg)

theorem affEMap_mulE (A : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin (3 + 1) → E3) (t : Dl) :
    affEMap (fun k => mulE A (w k)) t = mulE A (affEMap w t) := by
  simp only [affEMap, ContinuousMap.coe_mk]
  rw [mulE_sum]

theorem facesAvoid_mulE {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.det ≠ 0) {w : Fin (3 + 1) → E3}
    (hw : FacesAvoid w) : FacesAvoid (fun k => mulE A (w k)) := by
  intro t ht h
  rw [affEMap_mulE] at h
  exact hw t ht (mulE_eq_zero hA h)

/-- **Invariance under a path of invertible linear maps**: if `A` is joined to the identity by a path
of invertible matrices then `A` does not change the local degree of an affine simplex. -/
theorem degAff_mulE (A : Matrix (Fin 3) (Fin 3) ℝ) (γ : unitInterval → Matrix (Fin 3) (Fin 3) ℝ)
    (hγ : Continuous γ) (h0 : γ 0 = 1) (h1 : γ 1 = A) (hd : ∀ s, (γ s).det ≠ 0)
    (w : Fin (3 + 1) → E3) (hw : FacesAvoid w) :
    degAff (fun k => mulE A (w k)) (facesAvoid_mulE (h1 ▸ hd 1) hw) = degAff w hw := by
  refine (degAff_homotopy w _ hw _ (fun s k => mulE (γ s) (w k)) ?_ ?_ ?_ ?_).symm
  · intro k
    exact continuous_mulE hγ continuous_const
  · funext k; simp [h0, mulE_one]
  · funext k; simp [h1]
  · intro s
    exact facesAvoid_mulE (hd s) hw


/-! ### Orientation of affine tetrahedra and universality of `lamPos` -/

/-- The signed volume factor of the tetrahedron `w`: the determinant of the three edge vectors from
the first vertex (positive for a positively oriented tetrahedron). -/
def edgeDet (w : Fin (3 + 1) → E3) : ℝ :=
  Matrix.det (Matrix.of fun (i j : Fin 3) => (w i.succ - w 0) j)

theorem edgeDet_mulE (A : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin (3 + 1) → E3) :
    edgeDet (fun k => mulE A (v k)) = edgeDet v * A.det := by
  unfold edgeDet
  rw [← Matrix.det_transpose A, ← Matrix.det_mul]
  congr 1
  ext i j
  simp only [mulE, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  simp [Matrix.mulVec, dotProduct]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun x _ => by ring)

theorem edgeDet_rref (c : Fin (3 + 1) → ℝ) :
    edgeDet (rref c) = c 1 * c 0 * c 3 + c 1 * c 2 * c 3 + c 1 * c 2 * c 0 + c 0 * c 2 * c 3 := by
  simp [edgeDet, Matrix.det_fin_three, rref, rv, mk3]
  ring


/-- The matrix with columns `τ₁ w₁, τ₀ w₀, τ₂ w₂`, carrying the weighted reference tetrahedron onto `w`. -/
def Amat (τ : Fin (3 + 1) → ℝ) (w : Fin (3 + 1) → E3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => (![τ 1 • w 1, τ 0 • w 0, τ 2 • w 2] j) i

theorem Amat_carries (τ : Fin (3 + 1) → ℝ) (hτ : ∀ k, 0 < τ k) (w : Fin (3 + 1) → E3)
    (hrel : ∑ k, τ k • w k = 0) :
    w = fun k => mulE (Amat τ w) (rref (fun k => (τ k)⁻¹) k) := by
  have t0 := (hτ 0).ne'
  have t1 := (hτ 1).ne'
  have t2 := (hτ 2).ne'
  have t3 := (hτ 3).ne'
  have hr : ∀ i : Fin 3, τ 0 * w 0 i + τ 1 * w 1 i + τ 2 * w 2 i + τ 3 * w 3 i = 0 := by
    intro i
    have := congrArg (fun v : E3 => v i) hrel
    simpa [Fin.sum_univ_four, add_assoc] using this
  funext k
  ext i
  fin_cases k <;> fin_cases i <;>
    simp [mulE, Amat, rref, rv, mk3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    field_simp <;> linarith [hr 0, hr 1, hr 2]


theorem exists_carrier (w : Fin (3 + 1) → E3) (τ : Fin (3 + 1) → ℝ) (hτ : ∀ k, 0 < τ k)
    (hrel : ∑ k, τ k • w k = 0) (hdet : 0 < edgeDet w) :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, 0 < A.det ∧
      w = fun k => mulE A (rref (fun k => (τ k)⁻¹) k) := by
  have hc : ∀ k, 0 < (fun k => (τ k)⁻¹) k := fun k => inv_pos.mpr (hτ k)
  refine ⟨Amat τ w, ?_, Amat_carries τ hτ w hrel⟩
  have hw := Amat_carries τ hτ w hrel
  have e : edgeDet w = edgeDet (rref (fun k => (τ k)⁻¹)) * (Amat τ w).det := by
    calc edgeDet w = edgeDet (fun k => mulE (Amat τ w) (rref (fun k => (τ k)⁻¹) k)) :=
          congrArg edgeDet hw
      _ = _ := edgeDet_mulE (Amat τ w) _
  have hpos : 0 < edgeDet (rref (fun k => (τ k)⁻¹)) := by
    rw [edgeDet_rref]
    have := hc 0; have := hc 1; have := hc 2; have := hc 3
    positivity
  rw [e] at hdet
  exact pos_of_mul_pos_right hdet hpos.le |>.trans_le le_rfl

/-- A tetrahedron with a positive relation `∑ τₖ wₖ = 0` and positive orientation has no face
through the origin. -/
theorem facesAvoid_of_rel (w : Fin (3 + 1) → E3) (τ : Fin (3 + 1) → ℝ) (hτ : ∀ k, 0 < τ k)
    (hrel : ∑ k, τ k • w k = 0) (hdet : 0 < edgeDet w) : FacesAvoid w := by
  obtain ⟨A, hA, hw⟩ := exists_carrier w τ hτ hrel hdet
  rw [hw]
  exact facesAvoid_mulE hA.ne' (rref_facesAvoid _ (fun k => inv_pos.mpr (hτ k)))

/-- **Universality of `lamPos`**: every positively oriented tetrahedron with the origin in its
interior (a positive relation `∑ τₖ wₖ = 0`) has local degree `lamPos`. -/
theorem degAff_universal (w : Fin (3 + 1) → E3) (h : FacesAvoid w) (τ : Fin (3 + 1) → ℝ)
    (hτ : ∀ k, 0 < τ k) (hrel : ∑ k, τ k • w k = 0) (hdet : 0 < edgeDet w) :
    degAff w h = lamPos := by
  have hc : ∀ k, 0 < (fun k => (τ k)⁻¹) k := fun k => inv_pos.mpr (hτ k)
  obtain ⟨A, hdetA, hw⟩ := exists_carrier w τ hτ hrel hdet
  obtain ⟨γ, hγ, h0, h1, hd⟩ := conn_of_det_pos A hdetA
  have hr := rref_facesAvoid _ hc
  have step := degAff_mulE A γ hγ h0 h1 (fun s => (hd s).ne') _ hr
  calc degAff w h = degAff (fun k => mulE A (rref (fun k => (τ k)⁻¹) k))
        (facesAvoid_mulE hdetA.ne' hr) := degAff_congr _ _ _ _ hw
    _ = degAff (rref (fun k => (τ k)⁻¹)) hr := step
    _ = lamPos := degAff_rref _ hc

end TernaryPeriodPolynomials.Argument.Lemma33.Orient
