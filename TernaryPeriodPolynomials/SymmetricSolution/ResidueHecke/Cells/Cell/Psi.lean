module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Edge
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Trans
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Nbrs

@[expose] public section


/-!
# Lemma B.1, boundary route: a linear form on `Φ(RG₂)` detecting the Farey triangles

`exists_psi`: there is a `ℚ`-linear form `ψ` on `Φ(RG₂)` that vanishes on the image of `Φ(d₃)` and takes the value `1`
on the class `F2 t` of every Farey triangle `t`.  Consequently `[F2 t] ∉ range Φ(d₃)`.

The form is defined on chains by orienting the hexagon cells.  A cell of grade two has four lines; it is *of hexagon
type* if exactly three of them lie in the plane `Π = {x₀ = 0}`.  For an ordered tuple `ℓ` of such a cell,
`Psi4 ℓ = (-1)^{i} sign ob(y_a, y_b, y_c)` with `i` the position of the off-plane line and `(y_a, y_b, y_c)` the plane
vectors in order of appearance; it is alternating in `ℓ` (`Psi4_perm`), so `psiTil` (`psiTil_tupleVec`) is a
well-defined linear form on the oriented cell module with `psiTil [ℓ] = Psi4 ℓ`.  It is invariant under the radical
(`psiTil_twist_radZ`) and descends to the `U`-coinvariants (`psiPhi`).  On `F2 t = sign(ob a)·[(e₀, a₀, a₁, a₂)]`
it equals `sign(ob a)² = 1` (`psi_F2`).  It kills `d[T]` for every top cell `T` (`psiTil_dLin_single`): by transitivity
of `GL₃(ℤ)` on top cells `T = g T₀` and the ten neighbours of `T₀`, the only terms that can contribute are the two
plane neighbours `p ± q` of the two plane lines `p, q` of `T`, whose orientations are `D³` and `-D³` (`pair_cancel`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open CategoryTheory Finsupp TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing GeneralEisenstein
  TernaryPeriodPolynomials.Argument.Lemma33.Retract

section PlaneLines

/-- A line lies in the plane `x₀ = 0`. -/
def isPl (L : Line) : Prop := ∃ y, L = pl y

theorem isPl_pl (y : Fin 2 → ℤ) : isPl (pl y) := ⟨y, rfl⟩

theorem isPl_mk (u : Vec) : isPl (Line.mk u) ↔ u 0 = 0 := by
  constructor
  · rintro ⟨y, hy⟩
    unfold pl at hy
    rw [Line.mk_eq_mk] at hy
    rcases hy with h | h <;> (have h0 := congrFun h 0; simp at h0; omega)
  · intro h
    refine ⟨![u 1, u 2], ?_⟩
    unfold pl
    congr 1
    funext i
    fin_cases i <;> simp [h]

/-- A plane vector representing a plane line. -/
def yv (L : Line) : Fin 2 → ℤ := if h : isPl L then h.choose else 0

theorem yv_spec {L : Line} (h : isPl L) : L = pl (yv L) := by
  unfold yv
  rw [dite_eq_left h]
  exact h.choose_spec

theorem yv_pl (y : Fin 2 → ℤ) : yv (pl y) = y ∨ yv (pl y) = -y := by
  have h := yv_spec (isPl_pl y)
  rw [pl_eq_iff] at h
  exact h

/-- The orientation of a triple of plane lines. -/
def obL (a b c : Line) : ℤ := ob (yv a) (yv b) (yv c)

theorem ob_pm {y y' z z' w w' : Fin 2 → ℤ} (hy : y' = y ∨ y' = -y) (hz : z' = z ∨ z' = -z)
    (hw : w' = w ∨ w' = -w) : ob y' z' w' = ob y z w := by
  rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;>
    simp only [ob_neg_left, ob_neg_mid, ob_neg_right]

theorem obL_pl (a b c : Fin 2 → ℤ) : obL (pl a) (pl b) (pl c) = ob a b c :=
  ob_pm (yv_pl a) (yv_pl b) (yv_pl c)

theorem obL_swap01 (a b c : Line) : obL b a c = - obL a b c := ob_swap01 _ _ _
theorem obL_swap12 (a b c : Line) : obL a c b = - obL a b c := ob_swap12 _ _ _
theorem obL_swap02 (a b c : Line) : obL c b a = - obL a b c := ob_swap02 _ _ _

end PlaneLines

section Psi4

/-- The sign of an ordered hexagon cell: `(-1)^position · sign ob` when exactly one line is off the plane. -/
def Psi4 (ℓ : Fin 4 → Line) : ℤ :=
  if ¬ isPl (ℓ 0) ∧ isPl (ℓ 1) ∧ isPl (ℓ 2) ∧ isPl (ℓ 3) then Int.sign (obL (ℓ 1) (ℓ 2) (ℓ 3))
  else if isPl (ℓ 0) ∧ ¬ isPl (ℓ 1) ∧ isPl (ℓ 2) ∧ isPl (ℓ 3) then - Int.sign (obL (ℓ 0) (ℓ 2) (ℓ 3))
  else if isPl (ℓ 0) ∧ isPl (ℓ 1) ∧ ¬ isPl (ℓ 2) ∧ isPl (ℓ 3) then Int.sign (obL (ℓ 0) (ℓ 1) (ℓ 3))
  else if isPl (ℓ 0) ∧ isPl (ℓ 1) ∧ isPl (ℓ 2) ∧ ¬ isPl (ℓ 3) then - Int.sign (obL (ℓ 0) (ℓ 1) (ℓ 2))
  else 0

theorem Psi4_swap01 (ℓ : Fin 4 → Line) :
    Psi4 (fun k => ℓ (Equiv.swap (0 : Fin 4) 1 k)) = - Psi4 ℓ := by
  have h0 : Equiv.swap (0 : Fin 4) 1 0 = 1 := by decide
  have h1 : Equiv.swap (0 : Fin 4) 1 1 = 0 := by decide
  have h2 : Equiv.swap (0 : Fin 4) 1 2 = 2 := by decide
  have h3 : Equiv.swap (0 : Fin 4) 1 3 = 3 := by decide
  unfold Psi4
  simp only [h0, h1, h2, h3]
  by_cases b0 : isPl (ℓ 0) <;> by_cases b1 : isPl (ℓ 1) <;> by_cases b2 : isPl (ℓ 2) <;>
    by_cases b3 : isPl (ℓ 3) <;> simp [b0, b1, b2, b3, obL_swap01 (ℓ 0) (ℓ 1) (ℓ 3), obL_swap01 (ℓ 0) (ℓ 1) (ℓ 2), Int.sign_neg]

theorem Psi4_swap12 (ℓ : Fin 4 → Line) :
    Psi4 (fun k => ℓ (Equiv.swap (1 : Fin 4) 2 k)) = - Psi4 ℓ := by
  have h0 : Equiv.swap (1 : Fin 4) 2 0 = 0 := by decide
  have h1 : Equiv.swap (1 : Fin 4) 2 1 = 2 := by decide
  have h2 : Equiv.swap (1 : Fin 4) 2 2 = 1 := by decide
  have h3 : Equiv.swap (1 : Fin 4) 2 3 = 3 := by decide
  unfold Psi4
  simp only [h0, h1, h2, h3]
  by_cases b0 : isPl (ℓ 0) <;> by_cases b1 : isPl (ℓ 1) <;> by_cases b2 : isPl (ℓ 2) <;>
    by_cases b3 : isPl (ℓ 3) <;> simp [b0, b1, b2, b3, obL_swap01 (ℓ 1) (ℓ 2) (ℓ 3), obL_swap12 (ℓ 0) (ℓ 1) (ℓ 2), Int.sign_neg]

theorem Psi4_swap23 (ℓ : Fin 4 → Line) :
    Psi4 (fun k => ℓ (Equiv.swap (2 : Fin 4) 3 k)) = - Psi4 ℓ := by
  have h0 : Equiv.swap (2 : Fin 4) 3 0 = 0 := by decide
  have h1 : Equiv.swap (2 : Fin 4) 3 1 = 1 := by decide
  have h2 : Equiv.swap (2 : Fin 4) 3 2 = 3 := by decide
  have h3 : Equiv.swap (2 : Fin 4) 3 3 = 2 := by decide
  unfold Psi4
  simp only [h0, h1, h2, h3]
  by_cases b0 : isPl (ℓ 0) <;> by_cases b1 : isPl (ℓ 1) <;> by_cases b2 : isPl (ℓ 2) <;>
    by_cases b3 : isPl (ℓ 3) <;> simp [b0, b1, b2, b3, obL_swap12 (ℓ 1) (ℓ 2) (ℓ 3), obL_swap12 (ℓ 0) (ℓ 2) (ℓ 3), Int.sign_neg]

theorem Psi4_perm (π : Equiv.Perm (Fin 4)) (ℓ : Fin 4 → Line) :
    Psi4 (fun k => ℓ (π k)) = (((Equiv.Perm.sign π : ℤˣ) : ℤ)) * Psi4 ℓ := by
  have hcl := Equiv.Perm.mclosure_swap_castSucc_succ 3
  have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin 3 => Equiv.swap i.castSucc i.succ) := by
    rw [hcl]; trivial
  induction hπ using Submonoid.closure_induction generalizing ℓ with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [Equiv.Perm.sign_swap (Fin.castSucc_lt_succ).ne]
    fin_cases i
    · simpa using Psi4_swap01 ℓ
    · simpa using Psi4_swap12 ℓ
    · simpa using Psi4_swap23 ℓ
  | one => simp
  | mul x y _ _ hx hy =>
    have h1 : (fun k => ℓ ((x * y) k)) = fun k => (fun m => ℓ (x m)) (y k) := rfl
    rw [h1, hy (fun m => ℓ (x m)), hx ℓ, map_mul]
    push_cast
    ring

end Psi4

section PsiTilde

theorem card_of_graded (n : ℕ) (C : Graded n) : C.1.val.card = 6 - n := by
  have h : 6 - C.1.val.card = n := C.2
  have := C.1.card_le_six
  omega

theorem exists_enum (C : Graded 2) :
    ∃ ℓ : Fin 4 → Line, Function.Injective ℓ ∧ Finset.univ.image ℓ = C.1.val := by
  have hc : C.1.val.card = 4 := card_of_graded 2 C
  let e := C.1.val.equivFinOfCardEq hc
  refine ⟨fun i => (e.symm i : Line), fun i j h => e.symm.injective (Subtype.ext h), ?_⟩
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (e.symm i).2
  · intro hx
    exact ⟨e ⟨x, hx⟩, by simp⟩

theorem exists_perm_of_image_eq {k : ℕ} {ℓ ℓ' : Fin k → Line}
    (h' : Function.Injective ℓ') (himg : Finset.univ.image ℓ' = Finset.univ.image ℓ) :
    ∃ π : Equiv.Perm (Fin k), ∀ i, ℓ' i = ℓ (π i) := by
  have hex : ∀ i, ∃ j, ℓ j = ℓ' i := by
    intro i
    have : ℓ' i ∈ Finset.univ.image ℓ := by
      rw [← himg]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp this
    exact ⟨j, hj⟩
  choose π hπ using hex
  have hinj : Function.Injective π := by
    intro i k hik
    apply h'
    rw [← hπ i, ← hπ k, hik]
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.mp hinj), fun i => (hπ i).symm⟩

theorem TupleOK_enum (C : Graded 2) {ℓ : Fin 4 → Line} (hinj : Function.Injective ℓ)
    (himg : Finset.univ.image ℓ = C.1.val) : TupleOK 2 ℓ ∧ ∃ h : TupleOK 2 ℓ, tupleCell h = C := by
  have hok : TupleOK 2 ℓ := ⟨hinj, by rw [himg]; exact C.1.isCell, by norm_num⟩
  refine ⟨hok, hok, ?_⟩
  apply Subtype.ext; apply Cell.ext
  exact himg

/-- The chosen enumeration of a cell of grade two. -/
def enumC (C : Graded 2) : Fin 4 → Line := Classical.choose (exists_enum C)

theorem enumC_spec (C : Graded 2) :
    Function.Injective (enumC C) ∧ Finset.univ.image (enumC C) = C.1.val :=
  Classical.choose_spec (exists_enum C)

/-- The value of the functional on the cell `C`. -/
def cellPsiVal (C : Graded 2) : ℚ := ((Psi4 (enumC C) : ℤ) : ℚ) * sgnLab (enumC C)

/-- The functional on the free module on cells of grade two. -/
def psiTil : (Graded 2 →₀ ℚ) →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ cellPsiVal

theorem psiTil_single (C : Graded 2) (a : ℚ) : psiTil (single C a) = a * cellPsiVal C := by
  unfold psiTil
  rw [Finsupp.linearCombination_single, smul_eq_mul]

theorem psiTil_tupleVec {ℓ : Fin 4 → Line} (h : TupleOK 2 ℓ) : psiTil (tupleVec 2 ℓ) = (Psi4 ℓ : ℚ) := by
  rw [tupleVec_of_ok h, map_smul, psiTil_single, smul_eq_mul, one_mul]
  set C := tupleCell h with hC
  obtain ⟨hinjC, himgC⟩ := enumC_spec C
  have himg : Finset.univ.image ℓ = Finset.univ.image (enumC C) := by
    rw [himgC]; rfl
  obtain ⟨π, hπ⟩ := exists_perm_of_image_eq (ℓ := enumC C) (ℓ' := ℓ) h.1 himg
  have hℓ : ℓ = fun i => enumC C (π i) := funext hπ
  obtain ⟨hokC, -⟩ := TupleOK_enum C hinjC himgC
  rw [cellPsiVal]
  have e1 : Psi4 ℓ = ((Equiv.Perm.sign π : ℤˣ) : ℤ) * Psi4 (enumC C) := by
    rw [hℓ]; exact Psi4_perm π (enumC C)
  have e2 : sgnLab ℓ = (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℚ) * sgnLab (enumC C) := by
    rw [hℓ]; exact sgnLab_perm hokC π
  rw [e1, e2]
  have := sgnLab_sq (enumC C)
  push_cast
  linear_combination (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℚ) * (Psi4 (enumC C) : ℚ) * this

end PsiTilde

section Radical

theorem isPl_radZ_smul (w : Fin 2 → ℤ) (L : Line) : isPl (radZ w • L) ↔ isPl L := by
  induction L using Line.ind with
  | h x =>
    rw [smul_mk, isPl_mk, isPl_mk, mv_radZ]
    simp

theorem radZ_smul_of_isPl (w : Fin 2 → ℤ) {L : Line} (h : isPl L) : radZ w • L = L := by
  obtain ⟨y, rfl⟩ := h
  exact radZ_smul_pl w y

theorem Psi4_radZ (w : Fin 2 → ℤ) (ℓ : Fin 4 → Line) : Psi4 (fun i => radZ w • ℓ i) = Psi4 ℓ := by
  have h0 := isPl_radZ_smul w (ℓ 0)
  have h1 := isPl_radZ_smul w (ℓ 1)
  have h2 := isPl_radZ_smul w (ℓ 2)
  have h3 := isPl_radZ_smul w (ℓ 3)
  have f0 : isPl (ℓ 0) → radZ w • ℓ 0 = ℓ 0 := radZ_smul_of_isPl w
  have f1 : isPl (ℓ 1) → radZ w • ℓ 1 = ℓ 1 := radZ_smul_of_isPl w
  have f2 : isPl (ℓ 2) → radZ w • ℓ 2 = ℓ 2 := radZ_smul_of_isPl w
  have f3 : isPl (ℓ 3) → radZ w • ℓ 3 = ℓ 3 := radZ_smul_of_isPl w
  unfold Psi4
  simp only [h0, h1, h2, h3]
  by_cases b0 : isPl (ℓ 0) <;> by_cases b1 : isPl (ℓ 1) <;> by_cases b2 : isPl (ℓ 2) <;>
    by_cases b3 : isPl (ℓ 3) <;> simp [b0, b1, b2, b3, f0, f1, f2, f3]

theorem single_eq_tupleVec (C : Graded 2) :
    ∃ ℓ : Fin 4 → Line, ∃ _ : TupleOK 2 ℓ, ∃ h : TupleOK 2 ℓ, tupleCell h = C ∧
      single C (1 : ℚ) = sgnLab ℓ • tupleVec 2 ℓ := by
  obtain ⟨hinj, himg⟩ := enumC_spec C
  obtain ⟨hok, h, hc⟩ := TupleOK_enum C hinj himg
  refine ⟨enumC C, hok, h, hc, ?_⟩
  rw [tupleVec_of_ok h, hc, smul_smul, sgnLab_sq, one_smul]

theorem psiTil_twist_radZ (w : Fin 2 → ℤ) :
    psiTil ∘ₗ twistLin 2 (radZ w) = psiTil := by
  apply Finsupp.lhom_ext
  intro C a
  obtain ⟨ℓ, hok, h, hc, he⟩ := single_eq_tupleVec C
  have hs : single C a = a • single C (1 : ℚ) := by rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [LinearMap.comp_apply, hs, he]
  simp only [map_smul]
  rw [tupleVec_twist h (radZ w), psiTil_tupleVec (h.smul _), psiTil_tupleVec h, Psi4_radZ]

end Radical

section Descent

/-- The functional on `Φ(RG₂)`. -/
def psiPhi : (PhiX 2).V →ₗ[ℚ] ℚ :=
  Representation.Coinvariants.lift ((RGXph 2).ρ.comp U.subtype) psiTil (fun u => by
    obtain ⟨v, rfl⟩ := eU.surjective u
    exact psiTil_twist_radZ (Multiplicative.toAdd v))

theorem psiPhi_clsU (v : Graded 2 →₀ ℚ) : psiPhi (clsU 2 v) = psiTil v :=
  Representation.Coinvariants.lift_mk _ _ _ _

theorem ob_frame (g : GL2Z) :
    ob (frameVecs g 0) (frameVecs g 1) (frameVecs g 2) = g.val.det ^ 3 := by
  simp only [frameVecs, ob, D2, Matrix.det_fin_two]
  simp
  ring

theorem psi_F2 (t : FareyTree.Tri) : psiPhi (F2 t) = 1 := by
  obtain ⟨g, hg⟩ := t.2
  have ht : t = ⟨TernaryPoly.RankTwoAugmentedFrames.augmentedFrame g, g, rfl⟩ := Subtype.ext hg
  subst ht
  rw [F2_eq (isGenTriple_frame g)]
  obtain ⟨g', hg'⟩ := pi_surjective g
  set m : Fin 3 → Line := ![p1, p2, pl ![1, 1]] with hm
  have hmpl : ∀ i, ∃ y, m i = pl y := planar_hexP
  have hl : (fun i => pl (frameVecs g i)) = fun i => g'.1 • m i := by
    funext i
    fin_cases i
    · show pl (frameVecs g 0) = g'.1 • pl ![1, 0]
      rw [PH_smul_pl, hg']
      congr 1; funext j; fin_cases j <;> simp [frameVecs, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · show pl (frameVecs g 1) = g'.1 • pl ![0, 1]
      rw [PH_smul_pl, hg']
      congr 1; funext j; fin_cases j <;> simp [frameVecs, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · show pl (frameVecs g 2) = g'.1 • pl ![1, 1]
      rw [PH_smul_pl, hg']
      congr 1; funext j; fin_cases j <;> simp [frameVecs, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hok0 : TupleOK 2 (Fin.cons e0L m : Fin 4 → Line) := by
    have : (Fin.cons e0L m : Fin 4 → Line) = hexP := by
      funext i; fin_cases i <;> rfl
    rw [this]; exact tupleOK_hexP
  have hok : TupleOK 2 (Fin.cons e0L (fun i => pl (frameVecs g i)) : Fin 4 → Line) := by
    rw [hl]; exact (tupleOK_cons_e0_act_iff g' m hmpl).mpr hok0
  unfold G2
  rw [map_smul, psiPhi_clsU, psiTil_tupleVec hok]
  have hP : Psi4 (Fin.cons e0L (fun i => pl (frameVecs g i)) : Fin 4 → Line) =
      Int.sign (ob (frameVecs g 0) (frameVecs g 1) (frameVecs g 2)) := by
    have h0 : ¬ isPl e0L := by
      unfold e0L; rw [isPl_mk]; simp
    have hc : (Fin.cons e0L (fun i => pl (frameVecs g i)) : Fin 4 → Line) =
        ![e0L, pl (frameVecs g 0), pl (frameVecs g 1), pl (frameVecs g 2)] := by
      funext i; fin_cases i <;> rfl
    rw [hc]
    unfold Psi4
    simp [h0, isPl_pl, obL_pl]
  rw [hP, ob_frame]
  have hd := det_pm g
  rcases hd with h | h <;> simp [h]

end Descent

section Main

theorem mv_comb (g : IntegralGL3) (v0 v1 v2 : ℤ) :
    mv g ![v0, v1, v2] = v0 • mv g Cell0Geometry.e0 + v1 • mv g Cell0Geometry.e1 + v2 • mv g Cell0Geometry.e2 := by
  funext i
  simp [mv, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Cell0Geometry.e0, Cell0Geometry.e1,
    Cell0Geometry.e2]
  ring

theorem sum_nbrs_expand (g : IntegralGL3) (ℓ : Fin 3 → Line) :
    ∑ w ∈ nbrs (g • Cell0Geometry.T0set), Psi4 (Fin.cons w ℓ : Fin 4 → Line) =
      ∑ L ∈ nbrs Cell0Geometry.T0set, Psi4 (Fin.cons (g • L) ℓ : Fin 4 → Line) := by
  rw [nbrs_smul_gl, Finset.smul_finset_def, Finset.sum_image (fun a _ b _ h => MulAction.injective g h)]

theorem mk_plane (u : Vec) (h : u 0 = 0) : Line.mk u = pl ![u 1, u 2] := by
  unfold pl
  congr 1
  funext i
  fin_cases i <;> simp [h]

theorem pair_cancel (a b : Vec) (ha : a 0 = 0) (hb : b 0 = 0) :
    Int.sign (obL (Line.mk (a + b)) (Line.mk a) (Line.mk b)) +
      Int.sign (obL (Line.mk (a + -b)) (Line.mk a) (Line.mk b)) = 0 := by
  have h1 : (a + b) 0 = 0 := by simp [ha, hb]
  have h2 : (a + -b) 0 = 0 := by simp [ha, hb]
  rw [mk_plane _ h1, mk_plane _ h2, mk_plane a ha, mk_plane b hb, obL_pl, obL_pl]
  have : ob ![(a + -b) 1, (a + -b) 2] ![a 1, a 2] ![b 1, b 2] =
      - ob ![(a + b) 1, (a + b) 2] ![a 1, a 2] ![b 1, b 2] := by
    simp only [ob, D2]
    simp
    ring
  rw [this, Int.sign_neg]
  ring

theorem cons_eq_vec4 (w l0 l1 l2 : Line) : (Fin.cons w ![l0, l1, l2] : Fin 4 → Line) = ![w, l0, l1, l2] := by
  funext i; fin_cases i <;> rfl

/-- The psiTen terms, for the vectors `a, b, c`. -/
def psiTen (a b c : Vec) : ℤ :=
  Psi4 (Fin.cons (Line.mk (b + c)) ![Line.mk a, Line.mk b, Line.mk c] : Fin 4 → Line) +
  (Psi4 (Fin.cons (Line.mk (b + -c)) ![Line.mk a, Line.mk b, Line.mk c] : Fin 4 → Line) +
  (Psi4 (Fin.cons (Line.mk (a + b)) ![Line.mk a, Line.mk b, Line.mk c] : Fin 4 → Line) +
  (Psi4 (Fin.cons (Line.mk (a + -b)) ![Line.mk a, Line.mk b, Line.mk c] : Fin 4 → Line) +
  (Psi4 (Fin.cons (Line.mk (a + c)) ![Line.mk a, Line.mk b, Line.mk c] : Fin 4 → Line) +
  (Psi4 (Fin.cons (Line.mk (a + -c)) ![Line.mk a, Line.mk b, Line.mk c] : Fin 4 → Line) +
  (Psi4 (Fin.cons (Line.mk (a + b + c)) ![Line.mk a, Line.mk b, Line.mk c] : Fin 4 → Line) +
  (Psi4 (Fin.cons (Line.mk (a + b + -c)) ![Line.mk a, Line.mk b, Line.mk c] : Fin 4 → Line) +
  (Psi4 (Fin.cons (Line.mk (a + -b + c)) ![Line.mk a, Line.mk b, Line.mk c] : Fin 4 → Line) +
   Psi4 (Fin.cons (Line.mk (a + -b + -c)) ![Line.mk a, Line.mk b, Line.mk c] : Fin 4 → Line))))))))) 

theorem ten_k2 (a b c : Vec) (ha : a 0 = 0) (hb : b 0 = 0) (hc : c 0 ≠ 0) : psiTen a b c = 0 := by
  have hpc := pair_cancel a b ha hb
  unfold psiTen
  simp only [cons_eq_vec4]
  unfold Psi4
  simp [isPl_mk, ha, hb, hc]
  linarith

theorem ten_k1 (a b c : Vec) (ha : a 0 = 0) (hb : b 0 ≠ 0) (hc : c 0 = 0) : psiTen a b c = 0 := by
  have hpc := pair_cancel a c ha hc
  unfold psiTen
  simp only [cons_eq_vec4]
  unfold Psi4
  simp [isPl_mk, ha, hb, hc]
  linarith

theorem ten_k0 (a b c : Vec) (ha : a 0 ≠ 0) (hb : b 0 = 0) (hc : c 0 = 0) : psiTen a b c = 0 := by
  have hpc := pair_cancel b c hb hc
  unfold psiTen
  simp only [cons_eq_vec4]
  unfold Psi4
  simp [isPl_mk, ha, hb, hc]
  linarith

theorem ten_degenerate (a b c : Vec) (h : (a 0 ≠ 0 ∧ b 0 ≠ 0) ∨ (a 0 ≠ 0 ∧ c 0 ≠ 0) ∨ (b 0 ≠ 0 ∧ c 0 ≠ 0)) :
    psiTen a b c = 0 := by
  unfold psiTen
  simp only [cons_eq_vec4]
  unfold Psi4
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [isPl_mk, h1, h2]

theorem ten_zero (a b c : Vec) (h : ¬ (a 0 = 0 ∧ b 0 = 0 ∧ c 0 = 0)) : psiTen a b c = 0 := by
  by_cases ha : a 0 = 0 <;> by_cases hb : b 0 = 0 <;> by_cases hc : c 0 = 0
  · exact absurd ⟨ha, hb, hc⟩ h
  · exact ten_k2 a b c ha hb hc
  · exact ten_k1 a b c ha hb hc
  · exact ten_degenerate a b c (Or.inr (Or.inr ⟨hb, hc⟩))
  · exact ten_k0 a b c ha hb hc
  · exact ten_degenerate a b c (Or.inr (Or.inl ⟨ha, hc⟩))
  · exact ten_degenerate a b c (Or.inl ⟨ha, hb⟩)
  · exact ten_degenerate a b c (Or.inl ⟨ha, hb⟩)

theorem first_row_ne (g : IntegralGL3) :
    ¬ ((mv g Cell0Geometry.e0) 0 = 0 ∧ (mv g Cell0Geometry.e1) 0 = 0 ∧ (mv g Cell0Geometry.e2) 0 = 0) := by
  rintro ⟨h0, h1, h2⟩
  have hdet : (g : Matrix (Fin 3) (Fin 3) ℤ).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero (0 : Fin 3)
    intro j
    fin_cases j
    · simpa [mv, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Cell0Geometry.e0] using h0
    · simpa [mv, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Cell0Geometry.e1] using h1
    · simpa [mv, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Cell0Geometry.e2] using h2
  exact (Matrix.isUnits_det_units g).ne_zero hdet

theorem sum_nbrs_ten (g : IntegralGL3) :
    ∑ w ∈ nbrs (g • Cell0Geometry.T0set), Psi4 (Fin.cons w
      ![Line.mk (mv g Cell0Geometry.e0), Line.mk (mv g Cell0Geometry.e1), Line.mk (mv g Cell0Geometry.e2)] :
        Fin 4 → Line) = 0 := by
  have h := ten_zero (mv g Cell0Geometry.e0) (mv g Cell0Geometry.e1) (mv g Cell0Geometry.e2) (first_row_ne g)
  rw [sum_nbrs_expand, nbrs_T0]
  simp [Finset.sum_insert, Line.mk_eq_mk, smul_mk, mv_comb]
  unfold psiTen at h
  simp only [cons_eq_vec4] at h
  linarith

theorem T3t_smul (g : IntegralGL3) :
    (fun i => g • T3t i) =
      ![Line.mk (mv g Cell0Geometry.e0), Line.mk (mv g Cell0Geometry.e1), Line.mk (mv g Cell0Geometry.e2)] := by
  funext i
  fin_cases i
  · show g • e0L = _
    unfold e0L
    rw [smul_mk]; rfl
  · show g • pl ![1, 0] = _
    unfold pl
    rw [smul_mk]; rfl
  · show g • pl ![0, 1] = _
    unfold pl
    rw [smul_mk]; rfl

theorem image_smul_T3t (g : IntegralGL3) :
    Finset.univ.image (fun i => g • T3t i) = g • Cell0Geometry.T0set := by
  rw [Finset.smul_finset_def, ← image_T3t, Finset.image_image]
  rfl

theorem psiTil_dLin_single (T : Graded 3) : psiTil (dLin 2 (single T (1 : ℚ))) = 0 := by
  have hc : T.1.val.card = 3 := card_of_graded 3 T
  obtain ⟨g, hg⟩ := exists_gl_T0 T.1 hc
  have hok : TupleOK 3 (fun i => g • T3t i) := tupleOK_T3t.smul g
  have hcell : tupleCell hok = T := by
    apply Subtype.ext; apply Cell.ext
    change Finset.univ.image (fun i => g • T3t i) = T.1.val
    rw [image_smul_T3t, hg]
  have hsingle : single T (1 : ℚ) = sgnLab (fun i => g • T3t i) • tupleVec 3 (fun i => g • T3t i) := by
    rw [tupleVec_of_ok hok, hcell, smul_smul, sgnLab_sq, one_smul]
  rw [hsingle, map_smul, map_smul, tupleVec_d hok, map_sum]
  have hterm : ∀ w ∈ nbrs (Finset.univ.image (fun i => g • T3t i)),
      psiTil (tupleVec 2 (Fin.cons w (fun i => g • T3t i) : Fin 4 → Line)) =
        ((Psi4 (Fin.cons w (fun i => g • T3t i) : Fin 4 → Line) : ℤ) : ℚ) :=
    fun w hw => psiTil_tupleVec (hok.cons hw)
  rw [Finset.sum_congr rfl hterm, ← Int.cast_sum, image_smul_T3t, T3t_smul, sum_nbrs_ten]
  simp

theorem psiTil_dLin (z : Graded 3 →₀ ℚ) : psiTil (dLin 2 z) = 0 := by
  have h : psiTil ∘ₗ dLin 2 = 0 := by
    apply Finsupp.lhom_ext
    intro T a
    have hs : single T a = a • single T (1 : ℚ) := by rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [LinearMap.comp_apply, hs, map_smul, map_smul, psiTil_dLin_single, smul_zero]
    rfl
  exact LinearMap.congr_fun h z

/-- **The functional of the non-vanishing of the hexagon class**: a linear form on `Φ(RG₂)` that kills the
boundaries of `Φ(RG₃)` and takes the value `1` on the class of every Farey triangle. -/
theorem exists_psi : ∃ ψ : (PhiX 2).V →ₗ[ℚ] ℚ,
    (∀ x : (PhiX 3).V, ψ ((dPhi 2).hom x) = 0) ∧ ∀ t : FareyTree.Tri, ψ (F2 t) = 1 := by
  refine ⟨psiPhi, fun x => ?_, psi_F2⟩
  induction x using Representation.Coinvariants.induction_on with
  | h v =>
    have : (dPhi 2).hom (clsU 3 v) = clsU 2 (dLin 2 v) := rfl
    change psiPhi ((dPhi 2).hom (clsU 3 v)) = 0
    rw [this, psiPhi_clsU]
    exact psiTil_dLin v

end Main

end TernaryPeriodPolynomials.Argument.AppendixBResidue
