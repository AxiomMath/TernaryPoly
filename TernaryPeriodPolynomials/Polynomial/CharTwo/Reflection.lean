module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.Polynomial.CharTwo.NormGenerators

@[expose] public section


/-!
# Computing in `𝔽₂[x, y, z]` by evaluation of exponent lists

A polynomial over `𝔽₂` in `x, y, z` is represented by a list of exponent triples, one for each of
its monomials; `ev` is the polynomial denoted by such a list. Sum, product, powers, substitutions of
linear forms, the operators `sub₁`, `sub₂`, `norm` and `Π` (`piOperator`) are implemented on these
lists in a way that the kernel can evaluate, and each implementation is proved to correspond to
the polynomial operation. An identity between large explicit polynomials of `𝔽₂[x, y, z]` can thus
be established by computing both sides on lists (`decide +kernel`) instead of by expanding the
polynomials with `ring`.

The lists handled here are sorted lexicographically, so that equal polynomials have equal lists;
this is not needed for the correctness proofs, which hold for arbitrary lists.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.PolynomialReflection

open TernaryPoly.CharTwoNorm

/-- An exponent triple `(i, j, k)`, standing for the monomial `x^i y^j z^k`. -/
abbrev Mon := ℕ × ℕ × ℕ

/-- The monomial `x^i y^j z^k` of `𝔽₂[x, y, z]` with exponent triple `(i, j, k)`. -/
def mono (m : Mon) : Poly2 := X 0 ^ m.1 * X 1 ^ m.2.1 * X 2 ^ m.2.2

/-- The polynomial over `𝔽₂` that is the sum of the monomials in a list of exponent triples. -/
def ev (l : List Mon) : Poly2 := (l.map mono).sum

@[simp] theorem ev_nil : ev [] = 0 := rfl

@[simp] theorem ev_cons (m : Mon) (l : List Mon) : ev (m :: l) = mono m + ev l := by
  simp [ev]

theorem ev_append (l₁ l₂ : List Mon) : ev (l₁ ++ l₂) = ev l₁ + ev l₂ := by
  simp [ev]

theorem mono_add_self (m : Mon) : mono m + mono m = 0 := CharTwo.add_self_eq_zero _

theorem mono_mul (m n : Mon) :
    mono (m.1 + n.1, m.2.1 + n.2.1, m.2.2 + n.2.2) = mono m * mono n := by
  simp only [mono, pow_add]
  ring

theorem mono_zero : mono (0, 0, 0) = 1 := by
  simp [mono]

/-- Three-way lexicographic comparison of exponent triples: `0` for equal, `1` for less. -/
def cmp3 (a b : Mon) : ℕ :=
  if Nat.beq a.1 b.1 then
    (if Nat.beq a.2.1 b.2.1 then
      (if Nat.beq a.2.2 b.2.2 then 0 else if Nat.blt a.2.2 b.2.2 then 1 else 2)
     else if Nat.blt a.2.1 b.2.1 then 1 else 2)
  else if Nat.blt a.1 b.1 then 1 else 2

theorem cmp3_eq {a b : Mon} (h : cmp3 a b = 0) : a = b := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  simp only [cmp3] at h
  split at h
  · rename_i e1
    split at h
    · rename_i e2
      split at h
      · rename_i e3
        rw [Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3]
      · split at h <;> exact absurd h (by decide)
    · split at h <;> exact absurd h (by decide)
  · split at h <;> exact absurd h (by decide)

/-- Merge of two lexicographically sorted exponent lists, cancelling equal monomials
(characteristic two). The first argument is fuel. -/
def mergeAux : ℕ → List Mon → List Mon → List Mon
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, x :: s, [] => x :: s
  | n + 1, x :: s, y :: t =>
    match cmp3 x y with
    | 0 => mergeAux n s t
    | 1 => x :: mergeAux n s (y :: t)
    | _ => y :: mergeAux n (x :: s) t

theorem ev_mergeAux (n : ℕ) : ∀ a b : List Mon, ev (mergeAux n a b) = ev a + ev b := by
  induction n with
  | zero => intro a b; simp [mergeAux, ev_append]
  | succ n ih =>
    intro a b
    match a, b with
    | [], b => simp [mergeAux]
    | x :: s, [] => simp [mergeAux]
    | x :: s, y :: t =>
      simp only [mergeAux]
      split
      · rename_i h
        have hxy := cmp3_eq h
        subst hxy
        have := mono_add_self x
        simp only [ih, ev_cons]
        linear_combination (-1 : Poly2) * this
      · simp only [ih, ev_cons]
        ring
      · simp only [ih, ev_cons]
        ring

/-- Sum of two polynomials given as sorted exponent lists. -/
def addL (a b : List Mon) : List Mon := mergeAux (a.length + b.length) a b

theorem ev_addL (a b : List Mon) : ev (addL a b) = ev a + ev b := ev_mergeAux _ a b

/-- Multiplication of an exponent list by the monomial `m`. -/
def shiftL (m : Mon) (l : List Mon) : List Mon :=
  l.map fun n => (m.1 + n.1, m.2.1 + n.2.1, m.2.2 + n.2.2)

theorem ev_shiftL (m : Mon) (l : List Mon) : ev (shiftL m l) = mono m * ev l := by
  induction l with
  | nil => simp [shiftL]
  | cons n l ih =>
    simp only [shiftL, List.map_cons, ev_cons] at ih ⊢
    rw [mono_mul, ih]
    ring

/-- Product of two polynomials given as exponent lists. -/
def mulL (a b : List Mon) : List Mon := a.foldr (fun m acc => addL (shiftL m b) acc) []

theorem ev_mulL (a b : List Mon) : ev (mulL a b) = ev a * ev b := by
  induction a with
  | nil => simp [mulL]
  | cons m a ih =>
    simp only [mulL, List.foldr_cons] at ih ⊢
    rw [ev_addL, ev_shiftL, ih]
    simp only [ev_cons]
    ring

/-- Power by repeated squaring (the first argument is fuel). -/
def powAux : ℕ → List Mon → ℕ → List Mon
  | 0, _, _ => [(0, 0, 0)]
  | fuel + 1, t, n =>
    if n = 0 then [(0, 0, 0)]
    else
      let sq := mulL (powAux fuel t (n / 2)) (powAux fuel t (n / 2))
      if n % 2 = 1 then mulL t sq else sq

theorem ev_one : ev [(0, 0, 0)] = 1 := by
  simp [mono_zero]

theorem ev_powAux (t : List Mon) :
    ∀ fuel n : ℕ, n ≤ fuel → ev (powAux fuel t n) = ev t ^ n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    subst this
    simp [powAux, mono_zero]
  | succ fuel ih =>
    intro n hn
    by_cases h0 : n = 0
    · subst h0
      simp [powAux, mono_zero]
    · have hh := ih (n / 2) (by omega)
      simp only [powAux, h0, ite_false]
      by_cases hodd : n % 2 = 1
      · simp only [hodd, ite_true, ev_mulL, hh]
        rw [← pow_add, ← pow_succ']
        congr 1
        omega
      · simp only [hodd, ite_false, ev_mulL, hh]
        rw [← pow_add]
        congr 1
        omega

/-- The power `t ^ n` of a polynomial given as an exponent list. -/
def powL (t : List Mon) (n : ℕ) : List Mon := powAux n t n

theorem ev_powL (t : List Mon) (n : ℕ) : ev (powL t n) = ev t ^ n :=
  ev_powAux t n n le_rfl

/-- The list `[1, t, t², …, tᴺ]` of powers of `t`, as exponent lists. -/
def powTabAux (t : List Mon) : ℕ → List Mon → List (List Mon)
  | 0, cur => [cur]
  | n + 1, cur => cur :: powTabAux t n (mulL t cur)

theorem powTabAux_getElem (t : List Mon) :
    ∀ (N : ℕ) (cur : List Mon) (k : ℕ) (hk : k < (powTabAux t N cur).length),
      ev ((powTabAux t N cur)[k]) = ev cur * ev t ^ k := by
  intro N
  induction N with
  | zero =>
    intro cur k hk
    simp only [powTabAux, List.length_singleton] at hk
    have : k = 0 := by omega
    subst this
    simp [powTabAux]
  | succ N ih =>
    intro cur k hk
    cases k with
    | zero => simp [powTabAux]
    | succ k =>
      simp only [powTabAux, List.getElem_cons_succ]
      rw [ih (mulL t cur) k (by simpa [powTabAux] using hk), ev_mulL]
      ring

/-- The `k`-th power of `t`, read from a table of powers when available. -/
def tabPow (tab : List (List Mon)) (t : List Mon) (k : ℕ) : List Mon :=
  (tab[k]?).getD (powL t k)

theorem ev_tabPow (t : List Mon) (N k : ℕ) :
    ev (tabPow (powTabAux t N [(0, 0, 0)]) t k) = ev t ^ k := by
  unfold tabPow
  by_cases hk : k < (powTabAux t N [(0, 0, 0)]).length
  · rw [List.getElem?_eq_getElem hk, Option.getD_some, powTabAux_getElem t N _ k hk, ev_one,
      one_mul]
  · rw [List.getElem?_eq_none (not_lt.mp hk), Option.getD_none, ev_powL]

/-- A substitution `(x, y, z) ↦ (t₀, t₁, t₂)` given by three exponent lists. -/
abbrev Subst := List Mon × List Mon × List Mon

/-- The substitution of a triple of exponent lists, as a map `Fin 3 → Poly2`. -/
def toSub (t : Subst) : Fin 3 → Poly2 := ![ev t.1, ev t.2.1, ev t.2.2]

theorem bind₁_mono (f : Fin 3 → Poly2) (m : Mon) :
    bind₁ f (mono m) = f 0 ^ m.1 * f 1 ^ m.2.1 * f 2 ^ m.2.2 := by
  simp [mono]

/-- Substitution `(x, y, z) ↦ (t₀, t₁, t₂)` applied to an exponent list. The powers of each
`tᵢ` are read from tables of powers up to `N`. -/
def substL (N : ℕ) (t : Subst) (l : List Mon) : List Mon :=
  l.foldr (fun m acc =>
    addL (mulL (mulL (tabPow (powTabAux t.1 N [(0, 0, 0)]) t.1 m.1)
      (tabPow (powTabAux t.2.1 N [(0, 0, 0)]) t.2.1 m.2.1))
      (tabPow (powTabAux t.2.2 N [(0, 0, 0)]) t.2.2 m.2.2)) acc) []

theorem ev_substL (N : ℕ) (t : Subst) (l : List Mon) :
    bind₁ (toSub t) (ev l) = ev (substL N t l) := by
  induction l with
  | nil => simp [substL]
  | cons m l ih =>
    simp only [substL, List.foldr_cons] at ih ⊢
    rw [ev_addL, ev_mulL, ev_mulL, ev_tabPow, ev_tabPow, ev_tabPow, ← ih]
    simp [bind₁_mono, toSub]

/-! ### Linear forms and the operators `sub₁`, `sub₂`, `Π` -/

/-- The variable `x` as an exponent list. -/
def fx : List Mon := [(1, 0, 0)]
/-- The variable `y` as an exponent list. -/
def fy : List Mon := [(0, 1, 0)]
/-- The variable `z` as an exponent list. -/
def fz : List Mon := [(0, 0, 1)]
/-- The form `x + y` as an exponent list. -/
def fxy : List Mon := [(0, 1, 0), (1, 0, 0)]
/-- The form `x + z` as an exponent list. -/
def fxz : List Mon := [(0, 0, 1), (1, 0, 0)]
/-- The form `y + z` as an exponent list. -/
def fyz : List Mon := [(0, 0, 1), (0, 1, 0)]
/-- The form `x + y + z` as an exponent list. -/
def fxyz : List Mon := [(0, 0, 1), (0, 1, 0), (1, 0, 0)]

/-- The eighteen substitutions of `piSubstitutions`, as triples of exponent lists. -/
def piTriples : List Subst :=
  [(fy, fz, fxy), (fz, fy, fxz), (fx, fz, fxy), (fx, fz, fyz), (fxy, fz, fx), (fxy, fz, fy),
   (fz, fxyz, fxz), (fxyz, fz, fyz), (fx, fy, fxz), (fx, fy, fyz), (fy, fxz, fx),
   (fy, fxyz, fxy), (fxz, fy, fz), (fxyz, fy, fyz), (fx, fyz, fy), (fx, fxyz, fxy),
   (fx, fyz, fz), (fx, fxyz, fxz)]

theorem piSubstitutions_eq : piSubstitutions = piTriples.map toSub := by
  simp only [piSubstitutions, piTriples, toSub, List.map_cons, List.map_nil, List.cons.injEq,
    and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · funext i
    fin_cases i <;> simp [fx, fy, fz, fxy, fxz, fyz, fxyz, ev, mono] <;> ring

/-- `Π` on exponent lists. -/
def piL (l : List Mon) : List Mon :=
  piTriples.foldr (fun t acc => addL (substL 24 t l) acc) []

theorem piOperator_ev (l : List Mon) : piOperator (ev l) = ev (piL l) := by
  unfold piOperator piL
  rw [piSubstitutions_eq]
  generalize piTriples = ts
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, List.foldr_cons, ev_addL, ev_substL 24] at ih ⊢
    rw [ih]

/-- `sub₁` on exponent lists. -/
def sub1L (l : List Mon) : List Mon := substL 0 (fy, fxy, fz) l

/-- `sub₂` on exponent lists. -/
def sub2L (l : List Mon) : List Mon := substL 0 (fxy, fx, fz) l

theorem toSub_sub1 : toSub (fy, fxy, fz) = ![X 1, X 0 + X 1, X 2] := by
  funext i
  fin_cases i
  · simp [toSub, fy, ev, mono]
  · simp [toSub, fxy, ev, mono, add_comm]
  · simp [toSub, fz, ev, mono]

theorem toSub_sub2 : toSub (fxy, fx, fz) = ![X 0 + X 1, X 0, X 2] := by
  funext i
  fin_cases i
  · simp [toSub, fxy, ev, mono, add_comm]
  · simp [toSub, fx, ev, mono]
  · simp [toSub, fz, ev, mono]

theorem ev_sub₁ (l : List Mon) : sub₁ (ev l) = ev (sub1L l) := by
  rw [sub1L, ← ev_substL 0, toSub_sub1]
  rfl

theorem ev_sub₂ (l : List Mon) : sub₂ (ev l) = ev (sub2L l) := by
  rw [sub2L, ← ev_substL 0, toSub_sub2]
  rfl

/-- The characteristic-two norm on exponent lists. -/
def normL (l : List Mon) : List Mon := addL l (addL (sub1L l) (sub2L l))

theorem ev_norm (l : List Mon) : TernaryPoly.CharTwoNorm.norm (ev l) = ev (normL l) := by
  simp only [TernaryPoly.CharTwoNorm.norm, normL, ev_addL, ev_sub₁, ev_sub₂]
  ring

/-- `Π` of a polynomial computed by an exponent-list evaluation. -/
theorem piOperator_eq_of_reflect {P Q : Poly2} {lP lQ : List Mon} (hP : P = ev lP)
    (hQ : Q = ev lQ) (h : piL lP = lQ) : piOperator P = Q := by
  rw [hP, hQ, piOperator_ev, h]


/-! ### The standard polynomials `a, b, c, c₊, d₄, d₆, d₇` and the generators, as exponent lists -/

theorem ev_fx : ev fx = X 0 := by simp [fx, ev, mono]
theorem ev_fy : ev fy = X 1 := by simp [fy, ev, mono]
theorem ev_fz : ev fz = X 2 := by simp [fz, ev, mono]

/-- `a = x + y + z` as an exponent list. -/
def aL : List Mon := addL (addL fx fy) fz
/-- `b = xy + xz + yz` as an exponent list. -/
def bL : List Mon := addL (addL (mulL fx fy) (mulL fx fz)) (mulL fy fz)
/-- `c = xyz` as an exponent list. -/
def cL : List Mon := mulL (mulL fx fy) fz
/-- `c₊ = ab + c` as an exponent list. -/
def cplusL : List Mon := addL (mulL aL bL) cL
/-- `d₄ = a⁴ + b² + ac` as an exponent list. -/
def d4L : List Mon := addL (addL (powL aL 4) (powL bL 2)) (mulL aL cL)
/-- `d₆ = a²b² + a³c + abc + c²` as an exponent list. -/
def d6L : List Mon :=
  addL (addL (addL (mulL (powL aL 2) (powL bL 2)) (mulL (powL aL 3) cL)) (mulL (mulL aL bL) cL))
    (powL cL 2)
/-- `d₇ = a c c₊` as an exponent list. -/
def d7L : List Mon := mulL (mulL aL cL) cplusL

theorem ev_a : ev aL = a := by
  simp only [aL, ev_addL, ev_fx, ev_fy, ev_fz, a]

theorem ev_b : ev bL = b := by
  simp only [bL, ev_addL, ev_mulL, ev_fx, ev_fy, ev_fz, b]

theorem ev_c : ev cL = c := by
  simp only [cL, ev_mulL, ev_fx, ev_fy, ev_fz, c]

theorem ev_cplus : ev cplusL = cplus := by
  simp only [cplusL, ev_addL, ev_mulL, ev_a, ev_b, ev_c, cplus]

theorem ev_d4 : ev d4L = d4 := by
  simp only [d4L, ev_addL, ev_mulL, ev_powL, ev_a, ev_b, ev_c, d4]

theorem ev_d6 : ev d6L = d6 := by
  simp only [d6L, ev_addL, ev_mulL, ev_powL, ev_a, ev_b, ev_c, d6]

theorem ev_d7 : ev d7L = d7 := by
  simp only [d7L, ev_mulL, ev_a, ev_c, ev_cplus, d7]

/-- The list `basis j` as an exponent list. -/
def basisL : Fin 8 → List Mon :=
  ![[(0, 0, 0)], aL, addL (powL aL 2) bL, mulL aL bL, addL (powL aL 3) cL, mulL aL cplusL,
    mulL (powL aL 3) (addL (powL aL 2) bL),
    addL (addL (addL (powL aL 6) (mulL (powL aL 3) cL)) (powL bL 3)) (powL cL 2)]

theorem ev_basis (j : Fin 8) : ev (basisL j) = basis j := by
  fin_cases j <;>
    simp [basisL, basis, ev_addL, ev_mulL, ev_powL, ev_a, ev_b, ev_c, ev_cplus, mono_zero]

/-- `generator j = a c₊ B_j` as an exponent list. -/
def generatorL (j : Fin 8) : List Mon := mulL (mulL aL cplusL) (basisL j)

theorem ev_generator (j : Fin 8) : ev (generatorL j) = generator j := by
  simp only [generatorL, ev_mulL, ev_a, ev_cplus, ev_basis, generator]

/-- `oddGenerator j = generator j * d₇ ^ κ_j` as an exponent list. -/
def oddGeneratorL (j : Fin 8) : List Mon := mulL (generatorL j) (powL d7L (kappa j))

theorem ev_oddGenerator (j : Fin 8) : ev (oddGeneratorL j) = oddGenerator j := by
  simp only [oddGeneratorL, ev_mulL, ev_powL, ev_generator, ev_d7, oddGenerator]


/-- `Π` over the first `k` substitutions: on exponent lists. -/
def piTakeL (k : ℕ) (l : List Mon) : List Mon :=
  (piTriples.take k).foldr (fun t acc => addL (substL 24 t l) acc) []

/-- `Π` over the substitutions after the first `k`: on exponent lists. -/
def piDropL (k : ℕ) (l : List Mon) : List Mon :=
  (piTriples.drop k).foldr (fun t acc => addL (substL 24 t l) acc) []

theorem ev_sum_map_bind₁ (s : List Subst) (l : List Mon) :
    ((s.map toSub).map fun t => bind₁ t (ev l)).sum =
      ev (s.foldr (fun t acc => addL (substL 24 t l) acc) []) := by
  induction s with
  | nil => simp
  | cons t s ih =>
    simp only [List.map_cons, List.sum_cons, List.foldr_cons, ev_addL, ev_substL 24] at ih ⊢
    rw [ih]

theorem piTake_ev (k : ℕ) (l : List Mon) :
    ((piSubstitutions.take k).map fun t => bind₁ t (ev l)).sum = ev (piTakeL k l) := by
  rw [piSubstitutions_eq, ← List.map_take]
  exact ev_sum_map_bind₁ _ _

theorem piDrop_ev (k : ℕ) (l : List Mon) :
    ((piSubstitutions.drop k).map fun t => bind₁ t (ev l)).sum = ev (piDropL k l) := by
  rw [piSubstitutions_eq, ← List.map_drop]
  exact ev_sum_map_bind₁ _ _


theorem ev_eq_of_eq {P : Poly2} {l₁ l₂ : List Mon} (h : l₁ = l₂) (hP : ev l₂ = P) :
    ev l₁ = P := by
  rw [h, hP]

theorem piTake_eq_of_reflect {P Q : Poly2} {lP lQ : List Mon} (k : ℕ) (hP : P = ev lP)
    (hQ : Q = ev lQ) (h : piTakeL k lP = lQ) :
    ((piSubstitutions.take k).map fun t => bind₁ t P).sum = Q := by
  rw [hP, hQ, piTake_ev, h]

theorem piDrop_eq_of_reflect {P Q : Poly2} {lP lQ : List Mon} (k : ℕ) (hP : P = ev lP)
    (hQ : Q = ev lQ) (h : piDropL k lP = lQ) :
    ((piSubstitutions.drop k).map fun t => bind₁ t P).sum = Q := by
  rw [hP, hQ, piDrop_ev, h]

end TernaryPeriodPolynomials.Argument.PolynomialReflection
