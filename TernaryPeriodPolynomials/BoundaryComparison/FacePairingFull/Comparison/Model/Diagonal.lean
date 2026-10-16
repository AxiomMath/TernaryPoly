module

public import Mathlib

@[expose] public section


/-!
# The Alexander-Whitney cup product on homogeneous cochains and on the homotopy pullback of two face complexes

Generic algebra, independent of the arithmetic.  For a type `V` of vertices and an abelian group `A`, a homogeneous
`p`-cochain is a function `(Fin (p + 1) → V) → A` (`Ch V A p`), with the homogeneous coboundary `dif` (alternating sum
over the faces `x ∘ i.succAbove`) and, for a biadditive `β : A₁ →+ A₂ →+ A₃`, the Alexander-Whitney cup product
`cup β : Ch V A₁ p → Ch V A₂ q → Ch V A₃ (p + q)`, `(f ⌣ g)(x) = β (f (x ∘ front)) (g (x ∘ back))`.

* `dif_cup`: the Leibniz rule `d (f ⌣ g) = df ⌣ g + (-1)^p f ⌣ dg`, by the usual telescoping of the front and back faces.
* `Cone`: the cochains of the homotopy pullback of a line complex and a plane complex over a corner complex along
  additive restrictions `rL`, `rP` (degree `k + 1`: line and plane components of degree `k + 1`, corner component of
  degree `k`), with differential `coneD (l, p, c) = (dl, dp, rL l - rP p - dc)`.  A cocycle has `dc = rL l - rP p`.
* `coneCup`: the one-sided cup product `(l, p, c) ⌣ (l', p', c') = (l ⌣ l', p ⌣ p', c ⌣ rL l' + (-1)^a rP p ⌣ c')`
  (`a` the degree of the first factor), and `coneCup_leibniz_l`, `_p`, `_c`: the Leibniz rule
  `d (U ⌣ U') = dU ⌣ U' + (-1)^a U ⌣ dU'` componentwise, for restrictions multiplicative with respect to the pairings.

In the face-pairing model the boundary cup product `w ⌣ y^φ - γ` is the corner component of `(z, 0, w) ⌣ (y^φ, 0, ·)`
corrected by the coboundary of a vertex primitive `γ` of the line component.

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.ModelDiagonal

open Finset

/-- Homogeneous `p`-cochains on a vertex set `V` with values in `A`. -/
abbrev Ch (V A : Type) (p : ℕ) := (Fin (p + 1) → V) → A

theorem sum_split {M : Type} [AddCommMonoid M] (a b n : ℕ) (h : a + b = n) (F : Fin n → M) :
    ∑ i, F i = ∑ i : Fin a, F ⟨i, by omega⟩ + ∑ j : Fin b, F ⟨a + j, by omega⟩ := by
  subst h
  rw [Fin.sum_univ_add]
  rfl

variable {V : Type}

section

variable {A : Type} [AddCommGroup A]

/-- The homogeneous coboundary. -/
def dif {p : ℕ} (f : Ch V A p) : Ch V A (p + 1) :=
  fun x => ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • f (x ∘ i.succAbove)

end

/-- Front face: the first `p + 1` vertices. -/
def frontIdx (p n : ℕ) (h : p ≤ n) (j : Fin (p + 1)) : Fin (n + 1) := ⟨j, by omega⟩

/-- Back face: the last `q + 1` vertices of a `(p + q)`-simplex. -/
def backIdx (p q n : ℕ) (h : p + q = n) (j : Fin (q + 1)) : Fin (n + 1) := ⟨p + j, by omega⟩

section Core

variable {V : Type}

theorem core_identity {A : Type} [AddCommGroup A] (p q : ℕ)
    (T : (Fin (p + 1) → V) → (Fin (q + 1) → V) → A) (x : Fin (p + q + 2) → V) :
    ∑ i : Fin (p + q + 2), (-1 : ℤ) ^ (i : ℕ) •
        T ((x ∘ i.succAbove) ∘ frontIdx p (p + q) (by omega))
          ((x ∘ i.succAbove) ∘ backIdx p q (p + q) rfl) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        T ((x ∘ frontIdx (p + 1) (p + q + 1) (by omega)) ∘ i.succAbove)
          (x ∘ backIdx (p + 1) q (p + q + 1) (by omega)) +
      ((-1 : ℤ) ^ p) • ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
        T (x ∘ frontIdx p (p + q + 1) (by omega))
          ((x ∘ backIdx p (q + 1) (p + q + 1) (by omega)) ∘ j.succAbove) := by
  rw [sum_split (p + 1) (q + 1) (p + q + 2) (by omega)]
  rw [Fin.sum_univ_castSucc (fun i : Fin (p + 2) => (-1 : ℤ) ^ (i : ℕ) •
        T (((x ∘ frontIdx (p + 1) (p + q + 1) (by omega)) ∘ i.succAbove)) ((x ∘ backIdx (p + 1) q (p + q + 1) (by omega)))),
    Fin.sum_univ_succ (fun j : Fin (q + 2) => (-1 : ℤ) ^ (j : ℕ) •
        T ((x ∘ frontIdx p (p + q + 1) (by omega))) (((x ∘ backIdx p (q + 1) (p + q + 1) (by omega)) ∘ j.succAbove))), smul_add, smul_sum]
  -- function identities
  have e1 : ∀ a : Fin (p + 1),
      (x ∘ (⟨a, by omega⟩ : Fin (p + q + 2)).succAbove) ∘ frontIdx p (p + q) (by omega) =
        (x ∘ frontIdx (p + 1) (p + q + 1) (by omega)) ∘ (Fin.castSucc a).succAbove := by
    intro a
    funext j
    simp only [Function.comp]
    congr 1
    apply Fin.ext
    simp only [frontIdx, Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
    split_ifs <;> simp_all
  have e2 : ∀ a : Fin (p + 1),
      (x ∘ (⟨a, by omega⟩ : Fin (p + q + 2)).succAbove) ∘ backIdx p q (p + q) rfl =
        x ∘ backIdx (p + 1) q (p + q + 1) (by omega) := by
    intro a
    funext j
    simp only [Function.comp]
    congr 1
    apply Fin.ext
    simp only [backIdx, Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
    split_ifs <;> simp_all <;> omega
  have e3 : ∀ b : Fin (q + 1),
      (x ∘ (⟨p + 1 + b, by omega⟩ : Fin (p + q + 2)).succAbove) ∘ frontIdx p (p + q) (by omega) =
        x ∘ frontIdx p (p + q + 1) (by omega) := by
    intro b
    funext j
    simp only [Function.comp]
    congr 1
    apply Fin.ext
    simp only [frontIdx, Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
    split_ifs <;> simp_all
    omega
  have e4 : ∀ b : Fin (q + 1),
      (x ∘ (⟨p + 1 + b, by omega⟩ : Fin (p + q + 2)).succAbove) ∘ backIdx p q (p + q) rfl =
        (x ∘ backIdx p (q + 1) (p + q + 1) (by omega)) ∘ (Fin.succ b).succAbove := by
    intro b
    funext j
    simp only [Function.comp]
    congr 1
    apply Fin.ext
    simp only [backIdx, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> simp_all <;> omega
  have e5 : (x ∘ frontIdx (p + 1) (p + q + 1) (by omega)) ∘ (Fin.last (p + 1)).succAbove =
      x ∘ frontIdx p (p + q + 1) (by omega) := by
    funext j
    simp only [Function.comp]
    congr 1
    apply Fin.ext
    simp [frontIdx, Fin.succAbove]
  have e6 : (x ∘ backIdx p (q + 1) (p + q + 1) (by omega)) ∘ (0 : Fin (q + 2)).succAbove =
      x ∘ backIdx (p + 1) q (p + q + 1) (by omega) := by
    funext j
    simp only [Function.comp]
    congr 1
    apply Fin.ext
    simp [backIdx, Fin.succAbove]
    omega
  have hA : ∑ a : Fin (p + 1), (-1 : ℤ) ^ ((⟨a, by omega⟩ : Fin (p + q + 2)) : ℕ) •
      T (((x ∘ (⟨a, by omega⟩ : Fin (p + q + 2)).succAbove) ∘ frontIdx p (p + q) (by omega))) (((x ∘ (⟨a, by omega⟩ : Fin (p + q + 2)).succAbove) ∘ backIdx p q (p + q) rfl)) =
      ∑ a : Fin (p + 1), (-1 : ℤ) ^ ((Fin.castSucc a : Fin (p + 2)) : ℕ) •
        T (((x ∘ frontIdx (p + 1) (p + q + 1) (by omega)) ∘ (Fin.castSucc a).succAbove)) ((x ∘ backIdx (p + 1) q (p + q + 1) (by omega))) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [e1 a, e2 a]
    rfl
  have hB : ∑ b : Fin (q + 1), (-1 : ℤ) ^ ((⟨p + 1 + b, by omega⟩ : Fin (p + q + 2)) : ℕ) •
      T (((x ∘ (⟨p + 1 + b, by omega⟩ : Fin (p + q + 2)).succAbove) ∘ frontIdx p (p + q) (by omega))) (((x ∘ (⟨p + 1 + b, by omega⟩ : Fin (p + q + 2)).succAbove) ∘ backIdx p q (p + q) rfl)) =
      ∑ b : Fin (q + 1), (-1 : ℤ) ^ p • ((-1 : ℤ) ^ ((Fin.succ b : Fin (q + 2)) : ℕ) •
        T ((x ∘ frontIdx p (p + q + 1) (by omega))) (((x ∘ backIdx p (q + 1) (p + q + 1) (by omega)) ∘ (Fin.succ b).succAbove))) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [e3 b, e4 b, smul_smul, ← pow_add]
    congr 2
    simp only [Fin.val_succ]
    omega
  have hC : (-1 : ℤ) ^ ((Fin.last (p + 1) : Fin (p + 2)) : ℕ) •
        T (((x ∘ frontIdx (p + 1) (p + q + 1) (by omega)) ∘ (Fin.last (p + 1)).succAbove)) ((x ∘ backIdx (p + 1) q (p + q + 1) (by omega))) +
      (-1 : ℤ) ^ p • ((-1 : ℤ) ^ (((0 : Fin (q + 2)) : Fin (q + 2)) : ℕ) •
        T ((x ∘ frontIdx p (p + q + 1) (by omega))) (((x ∘ backIdx p (q + 1) (p + q + 1) (by omega)) ∘ (0 : Fin (q + 2)).succAbove))) = 0 := by
    rw [e5, e6, smul_smul]
    simp only [Fin.val_last, Fin.val_zero]
    rw [← add_smul]
    have : (-1 : ℤ) ^ (p + 1) + (-1 : ℤ) ^ p * (-1 : ℤ) ^ 0 = 0 := by
      rw [pow_succ]; ring
    rw [this, zero_smul]
  rw [hA, hB]
  linear_combination (norm := abel) (-1 : ℤ) • hC


end Core

section

variable {A₁ A₂ A₃ : Type} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]

/-- The Alexander-Whitney cup product of homogeneous cochains. -/
def cup (β : A₁ →+ A₂ →+ A₃) {p q n : ℕ} (h : p + q = n) (f : Ch V A₁ p) (g : Ch V A₂ q) :
    Ch V A₃ n :=
  fun x => β (f (x ∘ frontIdx p n (by omega))) (g (x ∘ backIdx p q n h))

theorem dif_cup (β : A₁ →+ A₂ →+ A₃) {p q n : ℕ} (h : p + q = n) (f : Ch V A₁ p) (g : Ch V A₂ q) :
    dif (cup β h f g) = cup β (n := n + 1) (p := p + 1) (q := q) (by omega) (dif f) g +
      ((-1 : ℤ) ^ p) • cup β (n := n + 1) (p := p) (q := q + 1) (by omega) f (dif g) := by
  subst h
  funext x
  have hL : dif (cup β rfl f g) x = ∑ i : Fin (p + q + 2), (-1 : ℤ) ^ (i : ℕ) •
      β (f ((x ∘ i.succAbove) ∘ frontIdx p (p + q) (by omega)))
        (g ((x ∘ i.succAbove) ∘ backIdx p q (p + q) rfl)) := rfl
  have hR1 : cup β (n := p + q + 1) (p := p + 1) (q := q) (by omega) (dif f) g x =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        β (f ((x ∘ frontIdx (p + 1) (p + q + 1) (by omega)) ∘ i.succAbove))
          (g (x ∘ backIdx (p + 1) q (p + q + 1) (by omega))) := by
    simp only [cup, dif, map_sum, map_zsmul, AddMonoidHom.finsetSum_apply]
    rfl
  have hR2 : cup β (n := p + q + 1) (p := p) (q := q + 1) (by omega) f (dif g) x =
      ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
        β (f (x ∘ frontIdx p (p + q + 1) (by omega)))
          (g ((x ∘ backIdx p (q + 1) (p + q + 1) (by omega)) ∘ j.succAbove)) := by
    simp only [cup, dif, map_sum, map_zsmul]
  have key := core_identity (V := V) (A := A₃) p q (fun u v => β (f u) (g v)) x
  rw [hL, Pi.add_apply, Pi.smul_apply, hR1, hR2]
  exact key

theorem cup_add_left (β : A₁ →+ A₂ →+ A₃) {p q n : ℕ} (h : p + q = n) (f f' : Ch V A₁ p)
    (g : Ch V A₂ q) : cup β h (f + f') g = cup β h f g + cup β h f' g := by
  funext x
  simp [cup]

theorem cup_add_right (β : A₁ →+ A₂ →+ A₃) {p q n : ℕ} (h : p + q = n) (f : Ch V A₁ p)
    (g g' : Ch V A₂ q) : cup β h f (g + g') = cup β h f g + cup β h f g' := by
  funext x
  simp [cup]

theorem cup_sub_left (β : A₁ →+ A₂ →+ A₃) {p q n : ℕ} (h : p + q = n) (f f' : Ch V A₁ p)
    (g : Ch V A₂ q) : cup β h (f - f') g = cup β h f g - cup β h f' g := by
  funext x
  simp [cup]

theorem cup_sub_right (β : A₁ →+ A₂ →+ A₃) {p q n : ℕ} (h : p + q = n) (f : Ch V A₁ p)
    (g g' : Ch V A₂ q) : cup β h f (g - g') = cup β h f g - cup β h f g' := by
  funext x
  simp [cup]

theorem cup_zsmul_left (β : A₁ →+ A₂ →+ A₃) {p q n : ℕ} (h : p + q = n) (m : ℤ) (f : Ch V A₁ p)
    (g : Ch V A₂ q) : cup β h (m • f) g = m • cup β h f g := by
  funext x
  simp [cup]

theorem cup_zsmul_right (β : A₁ →+ A₂ →+ A₃) {p q n : ℕ} (h : p + q = n) (m : ℤ) (f : Ch V A₁ p)
    (g : Ch V A₂ q) : cup β h f (m • g) = m • cup β h f g := by
  funext x
  simp [cup]

end

section

variable {A B : Type} [AddCommGroup A] [AddCommGroup B]

theorem dif_sub {p : ℕ} (f g : Ch V A p) : dif (f - g) = dif f - dif g := by
  funext x
  simp [dif, smul_sub, Finset.sum_sub_distrib]

theorem dif_zsmul {p : ℕ} (m : ℤ) (f : Ch V A p) : dif (m • f) = m • dif f := by
  funext x
  simp only [dif, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_comm]

theorem dif_add {p : ℕ} (f g : Ch V A p) : dif (f + g) = dif f + dif g := by
  funext x
  simp [dif, smul_add, Finset.sum_add_distrib]

/-- Apply an additive map to the values of a cochain. -/
def Ch.map (r : A →+ B) {p : ℕ} (f : Ch V A p) : Ch V B p := fun x => r (f x)

theorem dif_map (r : A →+ B) {p : ℕ} (f : Ch V A p) : dif (Ch.map r f) = Ch.map r (dif f) := by
  funext x
  simp [dif, Ch.map, map_sum]

end


theorem map_cup {A₁ A₂ A₃ B₁ B₂ B₃ : Type} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]
    [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃]
    (β : A₁ →+ A₂ →+ A₃) (β' : B₁ →+ B₂ →+ B₃) (r₁ : A₁ →+ B₁) (r₂ : A₂ →+ B₂) (r₃ : A₃ →+ B₃)
    (hm : ∀ x y, r₃ (β x y) = β' (r₁ x) (r₂ y)) {p q n : ℕ} (h : p + q = n)
    (f : Ch V A₁ p) (g : Ch V A₂ q) :
    Ch.map r₃ (cup β h f g) = cup β' h (Ch.map r₁ f) (Ch.map r₂ g) := by
  funext x
  simp [cup, Ch.map, hm]

section Cone

variable {AL AP AE : Type} [AddCommGroup AL] [AddCommGroup AP] [AddCommGroup AE]

/-- A cochain of the homotopy pullback of two face complexes over their common corner complex, in degree
`k + 1`: line and plane components of degree `k + 1` and a corner component of degree `k`. -/
@[ext] structure Cone (V : Type) (AL AP AE : Type) (k : ℕ) where
  l : Ch V AL (k + 1)
  p : Ch V AP (k + 1)
  c : Ch V AE k

/-- The differential of the cone: `d(l, p, c) = (dl, dp, rₗ l - rₚ p - dc)`. -/
def coneD (rL : AL →+ AE) (rP : AP →+ AE) {k : ℕ} (U : Cone V AL AP AE k) : Cone V AL AP AE (k + 1) :=
  ⟨dif U.l, dif U.p, Ch.map rL U.l - Ch.map rP U.p - dif U.c⟩

end Cone

section ConeCup

variable {AL₁ AL₂ AL₃ AP₁ AP₂ AP₃ AE₁ AE₂ AE₃ : Type}
  [AddCommGroup AL₁] [AddCommGroup AL₂] [AddCommGroup AL₃]
  [AddCommGroup AP₁] [AddCommGroup AP₂] [AddCommGroup AP₃]
  [AddCommGroup AE₁] [AddCommGroup AE₂] [AddCommGroup AE₃]
  (βL : AL₁ →+ AL₂ →+ AL₃) (βP : AP₁ →+ AP₂ →+ AP₃) (βE : AE₁ →+ AE₂ →+ AE₃)
  (rL₁ : AL₁ →+ AE₁) (rL₂ : AL₂ →+ AE₂) (rL₃ : AL₃ →+ AE₃)
  (rP₁ : AP₁ →+ AE₁) (rP₂ : AP₂ →+ AE₂) (rP₃ : AP₃ →+ AE₃)

/-- The cup product on the homotopy pullback: `(l, p, c) ⌣ (l', p', c') = (l ⌣ l', p ⌣ p',
c ⌣ rₗ l' + (-1)^{a} rₚ p ⌣ c')` where `a = k + 1` is the degree of the first factor. -/
def coneCup {a b m : ℕ} (h : a + b + 1 = m) (U : Cone V AL₁ AP₁ AE₁ a) (U' : Cone V AL₂ AP₂ AE₂ b) :
    Cone V AL₃ AP₃ AE₃ m where
  l := cup βL (p := a + 1) (q := b + 1) (n := m + 1) (by omega) U.l U'.l
  p := cup βP (p := a + 1) (q := b + 1) (n := m + 1) (by omega) U.p U'.p
  c := cup βE (p := a) (q := b + 1) (n := m) (by omega) U.c (Ch.map rL₂ U'.l) +
    ((-1 : ℤ) ^ (a + 1)) • cup βE (p := a + 1) (q := b) (n := m) (by omega) (Ch.map rP₁ U.p) U'.c

end ConeCup


section ConeLeibniz

variable {AL₁ AL₂ AL₃ AP₁ AP₂ AP₃ AE₁ AE₂ AE₃ : Type}
  [AddCommGroup AL₁] [AddCommGroup AL₂] [AddCommGroup AL₃]
  [AddCommGroup AP₁] [AddCommGroup AP₂] [AddCommGroup AP₃]
  [AddCommGroup AE₁] [AddCommGroup AE₂] [AddCommGroup AE₃]
  (βL : AL₁ →+ AL₂ →+ AL₃) (βP : AP₁ →+ AP₂ →+ AP₃) (βE : AE₁ →+ AE₂ →+ AE₃)
  (rL₁ : AL₁ →+ AE₁) (rL₂ : AL₂ →+ AE₂) (rL₃ : AL₃ →+ AE₃)
  (rP₁ : AP₁ →+ AE₁) (rP₂ : AP₂ →+ AE₂) (rP₃ : AP₃ →+ AE₃)
  (hL : ∀ x y, rL₃ (βL x y) = βE (rL₁ x) (rL₂ y))
  (hP : ∀ x y, rP₃ (βP x y) = βE (rP₁ x) (rP₂ y))

/-- **Leibniz rule for the cone cup product**, line component. -/
theorem coneCup_leibniz_l {a b m : ℕ} (h : a + b + 1 = m) (U : Cone V AL₁ AP₁ AE₁ a)
    (U' : Cone V AL₂ AP₂ AE₂ b) :
    (coneD rL₃ rP₃ (coneCup βL βP βE rL₂ rP₁ h U U')).l =
      (coneCup βL βP βE rL₂ rP₁ (a := a + 1) (b := b) (m := m + 1) (by omega)
        (coneD rL₁ rP₁ U) U').l +
      ((-1 : ℤ) ^ (a + 1)) • (coneCup βL βP βE rL₂ rP₁ (a := a) (b := b + 1) (m := m + 1)
        (by omega) U (coneD rL₂ rP₂ U')).l :=
  dif_cup βL (p := a + 1) (q := b + 1) (n := m + 1) (by omega) U.l U'.l

/-- **Leibniz rule for the cone cup product**, plane component. -/
theorem coneCup_leibniz_p {a b m : ℕ} (h : a + b + 1 = m) (U : Cone V AL₁ AP₁ AE₁ a)
    (U' : Cone V AL₂ AP₂ AE₂ b) :
    (coneD rL₃ rP₃ (coneCup βL βP βE rL₂ rP₁ h U U')).p =
      (coneCup βL βP βE rL₂ rP₁ (a := a + 1) (b := b) (m := m + 1) (by omega)
        (coneD rL₁ rP₁ U) U').p +
      ((-1 : ℤ) ^ (a + 1)) • (coneCup βL βP βE rL₂ rP₁ (a := a) (b := b + 1) (m := m + 1)
        (by omega) U (coneD rL₂ rP₂ U')).p :=
  dif_cup βP (p := a + 1) (q := b + 1) (n := m + 1) (by omega) U.p U'.p

include hL hP in
/-- **Leibniz rule for the cone cup product**, corner component. -/
theorem coneCup_leibniz_c {a b m : ℕ} (h : a + b + 1 = m) (U : Cone V AL₁ AP₁ AE₁ a)
    (U' : Cone V AL₂ AP₂ AE₂ b) :
    (coneD rL₃ rP₃ (coneCup βL βP βE rL₂ rP₁ h U U')).c =
      (coneCup βL βP βE rL₂ rP₁ (a := a + 1) (b := b) (m := m + 1) (by omega)
        (coneD rL₁ rP₁ U) U').c +
      ((-1 : ℤ) ^ (a + 1)) • (coneCup βL βP βE rL₂ rP₁ (a := a) (b := b + 1) (m := m + 1)
        (by omega) U (coneD rL₂ rP₂ U')).c := by
  have F1 := map_cup βL βE rL₁ rL₂ rL₃ hL (p := a + 1) (q := b + 1) (n := m + 1) (by omega) U.l U'.l
  have F2 := map_cup βP βE rP₁ rP₂ rP₃ hP (p := a + 1) (q := b + 1) (n := m + 1) (by omega) U.p U'.p
  have D1 := dif_cup βE (p := a) (q := b + 1) (n := m) (by omega) U.c (Ch.map rL₂ U'.l)
  have D2 := dif_cup βE (p := a + 1) (q := b) (n := m) (by omega) (Ch.map rP₁ U.p) U'.c
  simp only [coneD, coneCup]
  rw [F1, F2, dif_add, dif_zsmul, D1, D2, dif_map, dif_map]
  simp only [cup_sub_left, cup_sub_right, smul_sub, smul_add]
  rcases neg_one_pow_eq_or ℤ a with ha | ha <;>
    simp only [pow_succ, ha] <;> simp <;> abel

end ConeLeibniz


theorem cup_zero_left {A₁ A₂ A₃ : Type} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]
    (β : A₁ →+ A₂ →+ A₃) {p q n : ℕ} (h : p + q = n) (g : Ch V A₂ q) :
    cup β h (0 : Ch V A₁ p) g = 0 := by
  funext x
  simp [cup]

theorem cup_zero_right {A₁ A₂ A₃ : Type} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]
    (β : A₁ →+ A₂ →+ A₃) {p q n : ℕ} (h : p + q = n) (f : Ch V A₁ p) :
    cup β h f (0 : Ch V A₂ q) = 0 := by
  funext x
  simp [cup]

theorem Ch.map_zero {A B : Type} [AddCommGroup A] [AddCommGroup B] (r : A →+ B) {p : ℕ} :
    Ch.map r (0 : Ch V A p) = 0 := by
  funext x
  simp [Ch.map]

section ConeCocycle

variable {AL AP AE : Type} [AddCommGroup AL] [AddCommGroup AP] [AddCommGroup AE]

/-- A cone cochain is a cocycle: `dl = 0`, `dp = 0`, `dc = rₗ l - rₚ p`. -/
def Cone.IsCocycle (rL : AL →+ AE) (rP : AP →+ AE) {k : ℕ} (U : Cone V AL AP AE k) : Prop :=
  dif U.l = 0 ∧ dif U.p = 0 ∧ Ch.map rL U.l - Ch.map rP U.p - dif U.c = 0

theorem Cone.isCocycle_iff (rL : AL →+ AE) (rP : AP →+ AE) {k : ℕ} (U : Cone V AL AP AE k) :
    U.IsCocycle rL rP ↔ coneD rL rP U = ⟨0, 0, 0⟩ := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact Cone.ext h1 h2 h3
  · intro h
    exact ⟨congrArg Cone.l h, congrArg Cone.p h, congrArg Cone.c h⟩

end ConeCocycle

section ConeCupCocycle

variable {AL₁ AL₂ AL₃ AP₁ AP₂ AP₃ AE₁ AE₂ AE₃ : Type}
  [AddCommGroup AL₁] [AddCommGroup AL₂] [AddCommGroup AL₃]
  [AddCommGroup AP₁] [AddCommGroup AP₂] [AddCommGroup AP₃]
  [AddCommGroup AE₁] [AddCommGroup AE₂] [AddCommGroup AE₃]
  (βL : AL₁ →+ AL₂ →+ AL₃) (βP : AP₁ →+ AP₂ →+ AP₃) (βE : AE₁ →+ AE₂ →+ AE₃)
  (rL₁ : AL₁ →+ AE₁) (rL₂ : AL₂ →+ AE₂) (rL₃ : AL₃ →+ AE₃)
  (rP₁ : AP₁ →+ AE₁) (rP₂ : AP₂ →+ AE₂) (rP₃ : AP₃ →+ AE₃)
  (hL : ∀ x y, rL₃ (βL x y) = βE (rL₁ x) (rL₂ y))
  (hP : ∀ x y, rP₃ (βP x y) = βE (rP₁ x) (rP₂ y))

include hL hP in
/-- The cone cup product of two cocycles is a cocycle. -/
theorem coneCup_isCocycle {a b m : ℕ} (h : a + b + 1 = m) (U : Cone V AL₁ AP₁ AE₁ a)
    (U' : Cone V AL₂ AP₂ AE₂ b) (hU : U.IsCocycle rL₁ rP₁) (hU' : U'.IsCocycle rL₂ rP₂) :
    (coneCup βL βP βE rL₂ rP₁ h U U').IsCocycle rL₃ rP₃ := by
  rw [Cone.isCocycle_iff]
  have hU0 := (Cone.isCocycle_iff rL₁ rP₁ U).1 hU
  have hU0' := (Cone.isCocycle_iff rL₂ rP₂ U').1 hU'
  refine Cone.ext ?_ ?_ ?_
  · rw [coneCup_leibniz_l βL βP βE rL₁ rL₂ rL₃ rP₁ rP₂ rP₃ h U U', hU0, hU0']
    simp [coneCup, cup_zero_left, cup_zero_right]
  · rw [coneCup_leibniz_p βL βP βE rL₁ rL₂ rL₃ rP₁ rP₂ rP₃ h U U', hU0, hU0']
    simp [coneCup, cup_zero_left, cup_zero_right]
  · rw [coneCup_leibniz_c βL βP βE rL₁ rL₂ rL₃ rP₁ rP₂ rP₃ hL hP h U U', hU0, hU0']
    simp [coneCup, cup_zero_left, cup_zero_right, Ch.map_zero]

end ConeCupCocycle

/-- Precomposition of a cochain with a vertex map `ψ` and a map `σ` on the index set of its values. -/
def Ch.pre {G S S' M : Type} (ψ : G → G) (σ : S' → S) {p : ℕ} (f : Ch G (S → M) p) :
    Ch G (S' → M) p :=
  fun x s => f (fun i => ψ (x i)) (σ s)

theorem dif_pre {G S S' M : Type} [AddCommGroup M] (ψ : G → G) (σ : S' → S) {p : ℕ}
    (f : Ch G (S → M) p) : dif (Ch.pre ψ σ f) = Ch.pre ψ σ (dif f) := by
  funext x s
  simp [dif, Ch.pre, Finset.sum_apply]
  rfl

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.ModelDiagonal
