module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeSum

@[expose] public section


/-!
# Coset representatives for the Hecke operators of `Γ₁(3)`

Fix the double coset `Δ_p = Γ₁(3) [[1,0],[0,p]] Γ₁(3) = {M ∈ M₂(ℤ) : det M = p,
M ≡ [[1,*],[0,p]] mod 3}` for a prime `p ≠ 3`. Its right cosets `Γ₁(3) α` are represented by
* `α_j = [[1,j],[0,p]]`, `0 ≤ j < p` (index `some j`), and
* `α_∞ = ε_p · [[p,0],[0,1]]` (index `none`), where `ε_p = 1` if `p ≡ 1 mod 3` and `ε_p = -1` if
  `p ≡ 2 mod 3` (so that `α_∞ ≡ [[1,0],[0,p]] mod 3`); `ε_p` is the scalar matrix `heckeSign p none`.

These are the level-one representatives of `binaryHeckeRepresentative` (Sol port) twisted by the
sign `heckeSign`; the right action of `g ∈ Γ₁(3)` permutes them by the level-one permutation
`modularHeckePermutation p g`, and the twisted level-one transition matrices lie in `Γ₁(3)`
(`gamma1_of_transition`: a congruence computation modulo `3`). This gives the coset family
`tpFamily p` of `T_p`.

For `U_3 = Γ₁(3) [[1,0],[0,3]] Γ₁(3)` the representatives are `β_j = [[1,j],[0,3]]`, `j ∈ {0,1,2}`,
and `g = [[a,b],[c,d]] ∈ Γ₁(3)` acts by `j ↦ (j - b) mod 3` with the explicit transition
`[[a + j'c, (b + j'd - j(a + j'c))/3],[3c, d - cj]] ∈ Γ₁(3)` (`u3Family`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped MatrixGroups
open Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeCosets

open TernaryPeriodPolynomials
open LevelThreeHeckeSum

/-- `SL₂(ℤ) → GL₂(ℚ)`. -/
abbrev toGLQ : SL(2, ℤ) →* GL (Fin 2) ℚ :=
  (GeneralLinearGroup.map (Int.castRingHom ℚ)).comp SpecialLinearGroup.toGL

theorem real_toGLQ (g : SL(2, ℤ)) : real (toGLQ g) = SpecialLinearGroup.mapGL ℝ g :=
  Spectral.LevelOneHecke.map_toGL_eq_mapGL g

/-- An integer relation `A' g = γ A` gives the corresponding relation in `GL₂(ℚ)`. -/
theorem rat_relation {A A' : Matrix (Fin 2) (Fin 2) ℤ} {a a' : GL (Fin 2) ℚ}
    (ha : A.map (Int.castRingHom ℚ) = a.val) (ha' : A'.map (Int.castRingHom ℚ) = a'.val)
    {g γ : SL(2, ℤ)} (h : A' * g.val = γ.val * A) : a' * toGLQ g = toGLQ γ * a := by
  apply Units.ext
  have relation := congrArg ((Int.castRingHom ℚ).mapMatrix) h
  rw [map_mul, map_mul] at relation
  change A'.map (Int.castRingHom ℚ) * g.val.map (Int.castRingHom ℚ) =
    γ.val.map (Int.castRingHom ℚ) * A.map (Int.castRingHom ℚ) at relation
  rw [ha, ha'] at relation
  exact relation

/-- The same relation in `GL₂(ℝ)`. -/
theorem real_relation {a a' : GL (Fin 2) ℚ} {g γ : SL(2, ℤ)} (h : a' * toGLQ g = toGLQ γ * a) :
    real a' * SpecialLinearGroup.mapGL ℝ g = SpecialLinearGroup.mapGL ℝ γ * real a := by
  rw [← real_toGLQ, ← real_toGLQ, ← map_mul, ← map_mul, h]

/-- **Congruence of transitions.** If `A, A'` are integer matrices congruent to `[[1,*],[0,u]]`
modulo `3` with `u` a unit, `g ∈ Γ₁(3)`, `γ ∈ SL₂(ℤ)` and `A' g = γ A`, then `γ ∈ Γ₁(3)`. -/
theorem gamma1_of_transition {A A' : Matrix (Fin 2) (Fin 2) ℤ} {g γ : SL(2, ℤ)} {u : ZMod 3}
    (hu : u ≠ 0)
    (hA : ((A 0 0 : ℤ) : ZMod 3) = 1 ∧ ((A 1 0 : ℤ) : ZMod 3) = 0 ∧ ((A 1 1 : ℤ) : ZMod 3) = u)
    (hA' : ((A' 0 0 : ℤ) : ZMod 3) = 1 ∧ ((A' 1 0 : ℤ) : ZMod 3) = 0 ∧
      ((A' 1 1 : ℤ) : ZMod 3) = u)
    (hg : g ∈ CongruenceSubgroup.Gamma1 3) (h : A' * g.val = γ.val * A) :
    γ ∈ CongruenceSubgroup.Gamma1 3 := by
  rw [CongruenceSubgroup.Gamma1_mem] at hg ⊢
  have e : ∀ i j, (((A' * g.val) i j : ℤ) : ZMod 3) = (((γ.val * A) i j : ℤ) : ZMod 3) :=
    fun i j => by rw [h]
  have e00 := e 0 0
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul] at e00 e10 e11
  simp only [hA.1, hA.2.1, hA.2.2, hA'.1, hA'.2.1, hA'.2.2, hg.1, hg.2.1, hg.2.2, mul_one,
    mul_zero, add_zero, zero_mul, zero_add] at e00 e10 e11
  refine ⟨e00.symm, ?_, e10.symm⟩
  rw [← e10, zero_mul, zero_add] at e11
  exact (mul_eq_right₀ hu).mp e11.symm

section Tp

variable (p : Nat.Primes)

/-- The sign `ε_p` (on the index `none`) making `α_∞ ≡ [[1,0],[0,p]] mod 3`. -/
def heckeSign : Option (Fin p.val) → SL(2, ℤ)
  | none => if p.val % 3 = 2 then -1 else 1
  | some _ => 1

theorem heckeSign_mul_self (i : Option (Fin p.val)) : heckeSign p i * heckeSign p i = 1 := by
  cases i with
  | none => unfold heckeSign; split_ifs <;> simp
  | some _ => simp [heckeSign]

/-- The rational representatives `ε_i α_i` of `Γ₁(3) \ Δ_p`. -/
def tpRep (i : Option (Fin p.val)) : GL (Fin 2) ℚ :=
  toGLQ (heckeSign p i) * binaryHeckeRepresentative p i

/-- The integer matrices of the representatives. -/
def tpInt (i : Option (Fin p.val)) : Matrix (Fin 2) (Fin 2) ℤ :=
  (heckeSign p i).val * modularHeckeMatrix p i

theorem tpInt_rational (i : Option (Fin p.val)) :
    (tpInt p i).map (Int.castRingHom ℚ) = (tpRep p i).val := by
  have h := modularHeckeMatrix_rational p i
  unfold tpInt tpRep
  rw [Matrix.map_mul, h]
  rfl

theorem tpRep_real (i : Option (Fin p.val)) :
    real (tpRep p i) =
      SpecialLinearGroup.mapGL ℝ (heckeSign p i) *
        Spectral.LevelOneHecke.heckeMatrix p i := by
  unfold tpRep
  show GeneralLinearGroup.map (Rat.castHom ℝ) (_ * _) = _
  rw [map_mul]
  exact congrArg (· * _) (real_toGLQ _)

theorem tpRep_det_pos (i : Option (Fin p.val)) : 0 < ((tpRep p i).det : ℚ) := by
  have h : ((tpRep p i).det : ℚ) = (((tpInt p i).det : ℤ) : ℚ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← tpInt_rational]
    exact (RingHom.map_det (Int.castRingHom ℚ) (tpInt p i)).symm
  have hdet : (tpInt p i).det = p.val := by
    unfold tpInt
    rw [Matrix.det_mul, (heckeSign p i).property, one_mul, modularHeckeMatrix_det]
  rw [h, hdet]
  exact_mod_cast p.property.pos

variable {p}

theorem natCast_zmod_three_ne_zero (hp : p.val ≠ 3) : (p.val : ZMod 3) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  rcases p.property.eq_one_or_self_of_dvd 3 h with h | h
  · omega
  · exact hp h.symm

theorem mod_three_cases (hp : p.val ≠ 3) : p.val % 3 = 1 ∨ p.val % 3 = 2 := by
  have h := natCast_zmod_three_ne_zero hp
  rw [← ZMod.natCast_mod] at h
  have : p.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : p.val % 3
  · exact absurd rfl h
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem tpInt_cong (hp : p.val ≠ 3) (i : Option (Fin p.val)) :
    ((tpInt p i 0 0 : ℤ) : ZMod 3) = 1 ∧ ((tpInt p i 1 0 : ℤ) : ZMod 3) = 0 ∧
      ((tpInt p i 1 1 : ℤ) : ZMod 3) = (p.val : ZMod 3) := by
  have hcast : (p.val : ZMod 3) = ((p.val % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod _ _).symm
  cases i with
  | none =>
    unfold tpInt heckeSign
    rcases mod_three_cases hp with h | h
    · rw [ite_eq_right (by omega)]
      simp [modularHeckeMatrix, hcast, h]
    · rw [ite_eq_left h]
      simp [modularHeckeMatrix, hcast, h]
      decide
  | some j =>
    simp [tpInt, heckeSign, modularHeckeMatrix]

theorem tp_transition (hp : p.val ≠ 3) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma1 3)
    (i : Option (Fin p.val)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma1 3,
      real (tpRep p (modularHeckePermutation p g i)) * SpecialLinearGroup.mapGL ℝ g =
        SpecialLinearGroup.mapGL ℝ γ * real (tpRep p i) := by
  set j := modularHeckePermutation p g i
  have hM := modularHeckeTransition_matrix p g i
  have hs : (heckeSign p i).val * (heckeSign p i).val = 1 := by
    have := congrArg Subtype.val (heckeSign_mul_self p i)
    simpa using this
  have hint : tpInt p j * g.val =
      (heckeSign p j * modularHeckeTransition p g i * heckeSign p i).val * tpInt p i := by
    have hmul : ∀ A B : SL(2, ℤ), (A * B).val = A.val * B.val := fun _ _ => rfl
    unfold tpInt
    rw [hmul, hmul, Matrix.mul_assoc, hM,
      Matrix.mul_assoc (_ * _), ← Matrix.mul_assoc (heckeSign p i).val, hs, Matrix.one_mul,
      Matrix.mul_assoc]
  refine ⟨_, gamma1_of_transition (natCast_zmod_three_ne_zero hp) (tpInt_cong hp i)
    (tpInt_cong hp j) hg hint, ?_⟩
  exact real_relation (rat_relation (tpInt_rational p i) (tpInt_rational p j) hint)

/-- **The coset family of `T_p`** (`p ≠ 3`): representatives `[[1,j],[0,p]]` (`0 ≤ j < p`) and
`ε_p [[p,0],[0,1]]`. -/
def tpFamily (hp : p.val ≠ 3) : CosetFamily (Option (Fin p.val)) where
  rep := tpRep p
  det_pos := tpRep_det_pos p
  transition g hg := ⟨modularHeckePermutation p g, fun i => tp_transition hp hg i⟩

end Tp

section U3

/-- The prime `3`. -/
def primeThree : Nat.Primes := ⟨3, Nat.prime_three⟩

/-- The rational representatives `[[1,j],[0,3]]` of `Γ₁(3) \ Γ₁(3) diag(1,3) Γ₁(3)`. -/
def u3Rep (j : Fin 3) : GL (Fin 2) ℚ := binaryHeckeRepresentative primeThree (some j)

theorem u3Rep_det_pos (j : Fin 3) : 0 < ((u3Rep j).det : ℚ) := by
  have h : ((u3Rep j).det : ℚ) =
      (((modularHeckeMatrix primeThree (some j)).det : ℤ) : ℚ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, u3Rep, ← modularHeckeMatrix_rational]
    exact (RingHom.map_det (Int.castRingHom ℚ) _).symm
  rw [h, modularHeckeMatrix_det]
  norm_num [primeThree]

/-- The action `j ↦ (j - b) mod 3` of `g = [[a,b],[c,d]]` on the representatives of `U_3`. -/
def u3Fun (g : SL(2, ℤ)) (j : Fin 3) : Fin 3 :=
  ⟨(((j : ℤ) - g.val 0 1) % 3).toNat, by omega⟩

theorem u3Fun_injective (g : SL(2, ℤ)) : Function.Injective (u3Fun g) := by
  intro j₁ j₂ h
  have h' := congrArg Fin.val h
  simp only [u3Fun] at h'
  have := j₁.isLt
  have := j₂.isLt
  ext
  omega

/-- The permutation of the representatives of `U_3` induced by `g`. -/
def u3Perm (g : SL(2, ℤ)) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (u3Fun g) (Finite.injective_iff_bijective.mp (u3Fun_injective g))

theorem dvd_of_zmod_eq {x : ℤ} {r : ℤ} (h : ((x : ℤ) : ZMod 3) = (r : ZMod 3)) :
    (3 : ℤ) ∣ x - r :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub r x 3).mp h.symm

theorem u3_matrix (a b c d j j' q : ℤ) (hq : b + j' * d - j * (a + j' * c) = 3 * q) :
    !![1, j'; 0, 3] * !![a, b; c, d] = !![a + j' * c, q; 3 * c, d - c * j] * !![1, j; 0, 3] := by
  ext r s
  fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hq
  · ring

theorem u3_transition {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma1 3) (j : Fin 3) :
    ∃ γ ∈ CongruenceSubgroup.Gamma1 3,
      modularHeckeMatrix primeThree (some (u3Perm g j)) * g.val =
        γ.val * modularHeckeMatrix primeThree (some j) := by
  rw [CongruenceSubgroup.Gamma1_mem] at hg
  obtain ⟨a, b, c, d, hgv⟩ : ∃ a b c d : ℤ, g.val = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two g.val⟩
  have e00 : g.val 0 0 = a := by simp [hgv]
  have e01 : g.val 0 1 = b := by simp [hgv]
  have e10 : g.val 1 0 = c := by simp [hgv]
  have e11 : g.val 1 1 = d := by simp [hgv]
  have hdet : a * d - b * c = 1 := by
    have := g.property
    rwa [hgv, Matrix.det_fin_two_of] at this
  have ha : (3 : ℤ) ∣ a - 1 := dvd_of_zmod_eq (by rw [← e00, hg.1]; simp)
  have hd : (3 : ℤ) ∣ d - 1 := dvd_of_zmod_eq (by rw [← e11, hg.2.1]; simp)
  have hc : (3 : ℤ) ∣ c - 0 := dvd_of_zmod_eq (by rw [← e10, hg.2.2]; simp)
  have hj' : (((u3Perm g j : Fin 3) : ℕ) : ℤ) = ((j : ℤ) - b) % 3 := by
    simp only [u3Perm, Equiv.ofBijective_apply, u3Fun, e01]
    omega
  obtain ⟨j', hj'def⟩ : ∃ j' : ℤ, j' = (((u3Perm g j : Fin 3) : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hj'def] at hj'
  have hN : (3 : ℤ) ∣ b + j' * d - (j : ℤ) * (a + j' * c) := by
    have e : b + j' * d - (j : ℤ) * (a + j' * c) =
        (b + j' - j) + j' * (d - 1) - j * (a - 1) - j * j' * (c - 0) := by ring
    rw [e]
    refine Dvd.dvd.sub (Dvd.dvd.sub (Dvd.dvd.add ?_ (hd.mul_left _)) (ha.mul_left _))
      (hc.mul_left _)
    omega
  obtain ⟨q, hq⟩ := hN
  obtain ⟨c₁, hc₁⟩ := hc
  have hc' : c = 3 * c₁ := by linarith
  have h3 : ((3 : ℤ) : ZMod 3) = 0 := by decide
  have ha' : ((a : ℤ) : ZMod 3) = 1 := by rw [← e00, hg.1]
  have hd' : ((d : ℤ) : ZMod 3) = 1 := by rw [← e11, hg.2.1]
  have hγ : (!![a + j' * c, q; 3 * c, d - c * j] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + c * hq
  refine ⟨(⟨_, hγ⟩ : SL(2, ℤ)), ?_, ?_⟩
  · refine (CongruenceSubgroup.Gamma1_mem 3 _).mpr ?_
    change ((a + j' * c : ℤ) : ZMod 3) = 1 ∧ ((d - c * j : ℤ) : ZMod 3) = 1 ∧
      ((3 * c : ℤ) : ZMod 3) = 0
    simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, hc', h3, ha', hd']
    simp
  · have hM : ∀ i : Fin 3, modularHeckeMatrix primeThree (some i) = !![1, (i : ℤ); 0, 3] :=
      fun _ => rfl
    rw [hM, hM, hgv, ← hj'def]
    exact u3_matrix a b c d j j' q hq

theorem u3Int_rational (j : Fin 3) :
    (modularHeckeMatrix primeThree (some j)).map (Int.castRingHom ℚ) = (u3Rep j).val :=
  modularHeckeMatrix_rational primeThree (some j)

/-- **The coset family of `U_3`**: representatives `[[1,j],[0,3]]`, `j ∈ {0,1,2}`. -/
def u3Family : CosetFamily (Fin 3) where
  rep := u3Rep
  det_pos := u3Rep_det_pos
  transition g hg := ⟨u3Perm g, fun j => by
    obtain ⟨γ, hγ, h⟩ := u3_transition hg j
    exact ⟨γ, hγ, real_relation (rat_relation (u3Int_rational j) (u3Int_rational _) h)⟩⟩

end U3

end TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeCosets
