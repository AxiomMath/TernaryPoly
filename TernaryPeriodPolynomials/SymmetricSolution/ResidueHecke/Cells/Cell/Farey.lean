module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Orient
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FareyAction
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FareyRank

@[expose] public section


/-!
# Lemma B.1, boundary route: the classes of the Farey triangles in `Φ(RG_2)`

For a triangle `t` of the Farey complex with a triple `a` of primitive generators of its three lines
(`IsGenTriple`), `F2 t = G2 a` is independent of the choice of the triple, and
`ρ(g) F2 t = det(C) F2 (C • t)` for `g ∈ P_H` with block `C`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open CategoryTheory Finsupp TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing GeneralEisenstein
  TernaryPeriodPolynomials.Argument.Lemma33.Retract TernaryPoly.RankTwoAugmentedFrames
  TernaryPeriodPolynomials.Argument.FareyTree

/-- Primitive generators of the three lines of a triangle (in some order). -/
def IsGenTriple (t : Tri) (a : Fin 3 → IntegralVector) : Prop :=
  ∃ f : Fin 3 → RationalLine2, Function.Injective f ∧ Finset.univ.image f = t.1 ∧ ∀ i, IsGen (f i) (a i)

/-- The generators of the lines of the frame of `g`. -/
def frameVecs (g : GL2Z) : Fin 3 → IntegralVector :=
  ![fun i => g.val i 0, fun i => g.val i 1, fun i => g.val i 0 + g.val i 1]

theorem isGenTriple_frame (g : GL2Z) : IsGenTriple ⟨augmentedFrame g, g, rfl⟩ (frameVecs g) := by
  refine ⟨augmentedLine g, augmentedLine_injective g, rfl, fun i => ?_⟩
  fin_cases i
  · exact col_isGen g 0
  · exact col_isGen g 1
  · exact col_sum_isGen g

theorem IsGenTriple.perm {t : Tri} {a a' : Fin 3 → IntegralVector} (h : IsGenTriple t a)
    (h' : IsGenTriple t a') :
    ∃ π : Equiv.Perm (Fin 3), ∀ i, a' i = a (π i) ∨ a' i = -a (π i) := by
  obtain ⟨f, hf, himg, hgen⟩ := h
  obtain ⟨f', hf', himg', hgen'⟩ := h'
  have hex : ∀ i, ∃ j, f j = f' i := by
    intro i
    have : f' i ∈ Finset.univ.image f := by
      rw [himg, ← himg']; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp this
    exact ⟨j, hj⟩
  choose π hπ using hex
  have hinj : Function.Injective π := by
    intro i k hik
    apply hf'
    rw [← hπ i, ← hπ k, hik]
  refine ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.mp hinj), fun i => ?_⟩
  have h1 : IsGen (f (π i)) (a (π i)) := hgen _
  have h2 : IsGen (f (π i)) (a' i) := by
    have := hgen' i
    rwa [← hπ i] at this
  exact h1.eq_or_neg h2

theorem G2_eq_of_genTriple {t : Tri} {a a' : Fin 3 → IntegralVector} (h : IsGenTriple t a)
    (h' : IsGenTriple t a') : G2 a' = G2 a := by
  obtain ⟨π, hπ⟩ := h.perm h'
  have hε : ∀ i, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ a' i = ε • a (π i) := by
    intro i
    rcases hπ i with e | e
    · exact ⟨1, Or.inl rfl, by simp [e]⟩
    · exact ⟨-1, Or.inr rfl, by simp [e]⟩
  choose ε hε1 hε2 using hε
  have : a' = fun i => ε i • (fun k => a (π k)) i := funext hε2
  rw [this, G2_sign ε hε1, G2_perm π a]

/-- Every triangle has a generator triple. -/
theorem exists_genTriple (t : Tri) : ∃ a, IsGenTriple t a := by
  obtain ⟨g, hg⟩ := t.2
  have : t = ⟨augmentedFrame g, g, rfl⟩ := Subtype.ext hg
  exact ⟨frameVecs g, this ▸ isGenTriple_frame g⟩

/-- The class of a Farey triangle in `Φ(RG_2)`. -/
def F2 (t : Tri) : (PhiX 2).V := G2 (Classical.choose (exists_genTriple t))

theorem F2_eq {t : Tri} {a : Fin 3 → IntegralVector} (h : IsGenTriple t a) : F2 t = G2 a :=
  G2_eq_of_genTriple h (Classical.choose_spec (exists_genTriple t))

theorem tupleOK_cons_e0_act_iff (g : PH) {n k : ℕ} (m : Fin k → Line) (hm : ∀ i, ∃ y, m i = pl y) :
    TupleOK n (Fin.cons e0L (fun i => g.1 • m i) : Fin (k + 1) → Line) ↔
      TupleOK n (Fin.cons e0L m : Fin (k + 1) → Line) := by
  set v : Fin 2 → ℤ := fun i => (lamHom g : ℤ) * uvec g i with hv
  have hge : g.1 • e0L = radZ v • e0L := by
    change g.1 • Line.mk ![1, 0, 0] = radZ v • Line.mk ![1, 0, 0]
    rw [PH_smul_e0, ← wl_zero, radZ_smul_wl, add_zero]
  have hfix : ∀ i, radZ v • (g.1 • m i) = g.1 • m i := by
    intro i
    obtain ⟨y, hy⟩ := hm i
    rw [hy, PH_smul_pl, radZ_smul_pl]
  set A : Fin (k + 1) → Line := Fin.cons e0L (fun i => g.1 • m i) with hA
  have hB : (fun i => g.1 • (Fin.cons e0L m : Fin (k + 1) → Line) i) = fun i => radZ v • A i := by
    rw [smul_cons]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hA, hge]
    · simp [hA, hfix]
  have e1 := TupleOK.smul_iff (n := n) (Fin.cons e0L m : Fin (k + 1) → Line) g.1
  rw [hB] at e1
  have e2 := TupleOK.smul_iff (n := n) A (radZ v)
  exact e2.symm.trans e1

/-- **Transport in `Φ`** without hypothesis. -/
theorem phi_twist_cons_e0_full (g : PH) {n k : ℕ} (m : Fin k → Line) (hm : ∀ i, ∃ y, m i = pl y) :
    (PhiX n).ρ (QuotientGroup.mk g) (clsU n (tupleVec n (Fin.cons e0L m : Fin (k + 1) → Line))) =
      clsU n (tupleVec n (Fin.cons e0L (fun i => g.1 • m i) : Fin (k + 1) → Line)) := by
  by_cases h : TupleOK n (Fin.cons e0L m : Fin (k + 1) → Line)
  · exact phi_twist_cons_e0 g m hm h
  · have h2 : ¬ TupleOK n (Fin.cons e0L (fun i => g.1 • m i) : Fin (k + 1) → Line) :=
      fun h' => h ((tupleOK_cons_e0_act_iff g m hm).mp h')
    rw [tupleVec_of_not_ok h, tupleVec_of_not_ok h2, clsU_zero]
    exact map_zero _

theorem sign_det_mul (d x : ℤ) (hd : d = 1 ∨ d = -1) : Int.sign (d ^ 3 * x) = d * Int.sign x := by
  rcases hd with rfl | rfl <;> simp [Int.sign_neg]

theorem det_pm (C : GL2Z) : C.val.det = 1 ∨ C.val.det = -1 :=
  Int.isUnit_iff.mp (Matrix.isUnits_det_units C)

theorem G2_act (g : PH) (a : Fin 3 → IntegralVector) :
    (PhiX 2).ρ (QuotientGroup.mk g) (G2 a) =
      (((pi g).val.det : ℤ) : ℚ) • G2 (fun i => (pi g).val.mulVec (a i)) := by
  have hm : ∀ i : Fin 3, ∃ y, pl (a i) = pl y := fun i => ⟨a i, rfl⟩
  unfold G2
  rw [map_smul, phi_twist_cons_e0_full g (fun i => pl (a i)) hm]
  have hpl : (fun i : Fin 3 => g.1 • pl (a i)) = fun i => pl ((pi g).val.mulVec (a i)) := by
    funext i; exact PH_smul_pl g (a i)
  rw [hpl, smul_smul]
  have hob := ob_mulVec (pi g).val (a 0) (a 1) (a 2)
  have hsign := sign_det_mul (pi g).val.det (ob (a 0) (a 1) (a 2)) (det_pm (pi g))
  rw [hob, hsign]
  congr 1
  rcases det_pm (pi g) with h | h <;> simp [h]

/-- Chain-level form of the transport: `g (e₀, m) = U(v) (e₀, g m)` for a radical element `U(v)`. -/
theorem twist_cons_e0_eq (g : PH) {n k : ℕ} (m : Fin k → Line) (hm : ∀ i, ∃ y, m i = pl y)
    (h : TupleOK n (Fin.cons e0L m : Fin (k + 1) → Line)) :
    ∃ v : Fin 2 → ℤ, twistLin n g.1 (tupleVec n (Fin.cons e0L m : Fin (k + 1) → Line)) =
      twistLin n (radZ v) (tupleVec n (Fin.cons e0L (fun i => g.1 • m i) : Fin (k + 1) → Line)) := by
  set v : Fin 2 → ℤ := fun i => (lamHom g : ℤ) * uvec g i with hv
  have hge : g.1 • e0L = radZ v • e0L := by
    change g.1 • Line.mk ![1, 0, 0] = radZ v • Line.mk ![1, 0, 0]
    rw [PH_smul_e0, ← wl_zero, radZ_smul_wl, add_zero]
  have hfix : ∀ i, radZ v • (g.1 • m i) = g.1 • m i := by
    intro i
    obtain ⟨y, hy⟩ := hm i
    rw [hy, PH_smul_pl, radZ_smul_pl]
  refine ⟨v, ?_⟩
  have hokA := (tupleOK_cons_e0_act_iff g m hm).mpr h
  set A : Fin (k + 1) → Line := Fin.cons e0L (fun i => g.1 • m i) with hA
  have hB : (fun i => g.1 • (Fin.cons e0L m : Fin (k + 1) → Line) i) = fun i => radZ v • A i := by
    rw [smul_cons]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hA, hge]
    · simp [hA, hfix]
  rw [tupleVec_twist h g.1, hB, ← tupleVec_twist hokA (radZ v)]

/-- **Transport of the boundary in `Φ`.** -/
theorem phi_d_cons_e0 (g : PH) {n k : ℕ} (m : Fin k → Line) (hm : ∀ i, ∃ y, m i = pl y) :
    (PhiX n).ρ (QuotientGroup.mk g)
        (clsU n (dLin n (tupleVec (n + 1) (Fin.cons e0L m : Fin (k + 1) → Line)))) =
      clsU n (dLin n (tupleVec (n + 1) (Fin.cons e0L (fun i => g.1 • m i) : Fin (k + 1) → Line))) := by
  by_cases h : TupleOK (n + 1) (Fin.cons e0L m : Fin (k + 1) → Line)
  · obtain ⟨v, hv⟩ := twist_cons_e0_eq g m hm h
    rw [phi_act, ← dLin_twist, hv, dLin_twist, clsU_radZ]
  · have h2 : ¬ TupleOK (n + 1) (Fin.cons e0L (fun i => g.1 • m i) : Fin (k + 1) → Line) :=
      fun h' => h ((tupleOK_cons_e0_act_iff g m hm).mp h')
    rw [tupleVec_of_not_ok h, tupleVec_of_not_ok h2, map_zero, clsU_zero]
    exact map_zero _

theorem frameVecs_mul (C h : GL2Z) :
    frameVecs (C * h) = fun i => C.val.mulVec (frameVecs h i) := by
  funext i j
  fin_cases i <;> simp [frameVecs, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, mul_add,
    Finset.sum_add_distrib]

/-- The triangle of a frame. -/
def triOf (h : GL2Z) : Tri := ⟨augmentedFrame h, h, rfl⟩

theorem smul_triOf (C h : GL2Z) : C • triOf h = triOf (C * h) :=
  Subtype.ext (by rw [tri_smul_val]; exact smul_frame C h)

theorem F2_frame (h : GL2Z) : F2 (triOf h) = G2 (frameVecs h) :=
  F2_eq (isGenTriple_frame h)

/-- **Equivariance of the triangle classes.** -/
theorem F2_act (g : PH) (t : Tri) :
    (PhiX 2).ρ (QuotientGroup.mk g) (F2 t) = (((pi g).val.det : ℤ) : ℚ) • F2 ((pi g) • t) := by
  obtain ⟨h, hh⟩ := t.2
  have ht : t = triOf h := Subtype.ext hh
  subst ht
  rw [smul_triOf, F2_frame, F2_frame, G2_act, frameVecs_mul]

/-- The boundary of the hexagon class of a triangle vanishes. -/
theorem F2_boundary (t : Tri) :
    ((TernaryPeriodPolynomials.Argument.HochschildSerre.Phi U).map
      ((Rep.resFunctor PH.subtype).map (dRG 1))).hom (F2 t) = 0 := by
  obtain ⟨h, hh⟩ := t.2
  have ht : t = triOf h := Subtype.ext hh
  subst ht
  rw [F2_frame]
  obtain ⟨c, hc⟩ := pi_surjective h
  unfold G2
  rw [map_smul]
  have hm : ∀ i : Fin 3, ∃ y, (![p1, p2, pl ![1, 1]] : Fin 3 → Line) i = pl y := planar_hexP
  have key := phi_d_cons_e0 (n := 1) c _ hm
  have hpl : (fun i : Fin 3 => c.1 • (![p1, p2, pl ![1, 1]] : Fin 3 → Line) i) =
      fun i => pl (frameVecs h i) := by
    funext i
    fin_cases i
    · change c.1 • pl ![1, 0] = pl (frameVecs h 0)
      rw [PH_smul_pl, hc]
      congr 1
      funext j; fin_cases j <;> simp [frameVecs, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · change c.1 • pl ![0, 1] = pl (frameVecs h 1)
      rw [PH_smul_pl, hc]
      congr 1
      funext j; fin_cases j <;> simp [frameVecs, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · change c.1 • pl ![1, 1] = pl (frameVecs h 2)
      rw [PH_smul_pl, hc]
      congr 1
      funext j; fin_cases j <;> simp [frameVecs, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hpl] at key
  have hh0 : clsU 1 (dLin 1 (tupleVec 2 (Fin.cons e0L (![p1, p2, pl ![1, 1]] : Fin 3 → Line) : Fin 4 → Line))) = 0 :=
    phi_d_hexP
  rw [hh0, map_zero] at key
  rw [phi_d]
  rw [← key]
  simp

end TernaryPeriodPolynomials.Argument.AppendixBResidue
