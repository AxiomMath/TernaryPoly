module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.TreeCd

@[expose] public section


/-!
# The line as a tree: `ℤ` and `ℤ²` have cohomological dimension `≤ 1`, `≤ 2`

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open CategoryTheory CategoryTheory.Limits
section Line

/-- `Multiplicative ℤ` acts on `ℤ` by translation. -/
@[instance_reducible]
def lineActV : MulAction (Multiplicative ℤ) ℤ where
  smul q n := n + Multiplicative.toAdd q
  one_smul n := by
    show n + Multiplicative.toAdd (1 : Multiplicative ℤ) = n
    simp
  mul_smul q q' n := by
    show n + Multiplicative.toAdd (q * q') = (n + Multiplicative.toAdd q') + Multiplicative.toAdd q
    simp [toAdd_mul]
    ring

/-- … and on the oriented edges `(n, b)`: `b = false` is the edge `n → n + 1`, `b = true` is `n + 1 → n`. -/
@[instance_reducible]
def lineActE : MulAction (Multiplicative ℤ) (ℤ × Bool) where
  smul q e := (e.1 + Multiplicative.toAdd q, e.2)
  one_smul e := by
    show (e.1 + Multiplicative.toAdd (1 : Multiplicative ℤ), e.2) = e
    simp
  mul_smul q q' e := by
    show (e.1 + Multiplicative.toAdd (q * q'), e.2) = ((e.1 + Multiplicative.toAdd q') + Multiplicative.toAdd q, e.2)
    simp only [toAdd_mul]
    ext <;> simp [add_comm, add_left_comm]

/-- The potential of an edge function on the line. -/
def potZ {A : Type} [AddCommGroup A] (f : ℤ → A) : ℤ → A
  | Int.ofNat m => ∑ i ∈ Finset.range m, f (i : ℤ)
  | Int.negSucc m => -∑ i ∈ Finset.range (m + 1), f (-1 - (i : ℤ))

theorem potZ_succ {A : Type} [AddCommGroup A] (f : ℤ → A) (n : ℤ) : potZ f (n + 1) - potZ f n = f n := by
  rcases n with m | m
  · show (∑ i ∈ Finset.range (m + 1), f (i : ℤ)) - ∑ i ∈ Finset.range m, f (i : ℤ) = f (m : ℤ)
    rw [Finset.sum_range_succ]
    simp
  · rcases m with _ | m
    · show (∑ i ∈ Finset.range 0, f (i : ℤ)) - -∑ i ∈ Finset.range (0 + 1), f (-1 - (i : ℤ)) = f (Int.negSucc 0)
      simp
    · show -∑ i ∈ Finset.range (m + 1), f (-1 - (i : ℤ)) - -∑ i ∈ Finset.range (m + 1 + 1), f (-1 - (i : ℤ)) =
        f (Int.negSucc (m + 1))
      rw [Finset.sum_range_succ _ (m + 1)]
      have : f (-1 - ((m + 1 : ℕ) : ℤ)) = f (Int.negSucc (m + 1)) := by
        congr 1
        rw [Int.negSucc_eq]
        push_cast
        ring
      rw [this]
      abel

/-- **The line**, a tree with a free action of `ℤ`. -/
def lineTree : TreeData (Multiplicative ℤ) where
  Vt := ℤ
  Et := ℤ × Bool
  mulV := lineActV
  mulE := lineActE
  swap e := (e.1, !e.2)
  src e := if e.2 then e.1 + 1 else e.1
  tgt e := if e.2 then e.1 else e.1 + 1
  src_smul q e := by
    show (if e.2 then e.1 + Multiplicative.toAdd q + 1 else e.1 + Multiplicative.toAdd q) =
      (if e.2 then e.1 + 1 else e.1) + Multiplicative.toAdd q
    split_ifs <;> ring
  tgt_smul q e := by
    show (if e.2 then e.1 + Multiplicative.toAdd q else e.1 + Multiplicative.toAdd q + 1) =
      (if e.2 then e.1 else e.1 + 1) + Multiplicative.toAdd q
    split_ifs <;> ring
  swap_smul q e := rfl
  src_swap e := by
    rcases e with ⟨n, b⟩
    cases b <;> rfl
  swap_swap e := by
    rcases e with ⟨n, b⟩
    simp
  free_v q v h := by
    have : v + Multiplicative.toAdd q = v := h
    have h0 : Multiplicative.toAdd q = 0 := by omega
    exact Multiplicative.toAdd.injective (by simpa using h0)
  free_e q e h := by
    have : e.1 + Multiplicative.toAdd q = e.1 := congrArg Prod.fst h
    have h0 : Multiplicative.toAdd q = 0 := by omega
    exact Multiplicative.toAdd.injective (by simpa using h0)
  nonempty_v := ⟨0⟩
  conn A _ P h v w := by
    have step : ∀ n : ℤ, P (n + 1) = P n := fun n => h (n, false)
    have key : ∀ n : ℤ, P n = P 0 := by
      intro n
      induction n using Int.induction_on with
      | zero => rfl
      | succ i ih => rw [step, ih]
      | pred i ih =>
        have := step (-(i : ℤ) - 1)
        rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at this
        rw [← ih, this]
    exact (key v).trans (key w).symm
  pot A _ _ F hF := by
    refine ⟨potZ (fun n => F (n, false)), ?_⟩
    rintro ⟨n, b⟩
    cases b
    · exact potZ_succ (fun n => F (n, false)) n
    · have h1 := hF (n, true)
      have h2 := potZ_succ (fun n => F (n, false)) n
      have h3 : F (n, false) = -F (n, true) := by
        have : F (n, !true) = -F (n, true) := h1
        simpa using this
      show potZ (fun n => F (n, false)) n - potZ (fun n => F (n, false)) (n + 1) = F (n, true)
      rw [← neg_sub, h2, h3, neg_neg]

end Line

section Dim

variable {k : Type} [CommRing k] [Algebra ℚ k] [Invertible (2 : k)]

/-- `ℤ` has cohomological dimension `≤ 1`. -/
theorem cdLe_int : CdLe k (Multiplicative ℤ) 1 := by
  have h0 : CdLe k (MonoidHom.id (Multiplicative ℤ)).ker 0 := by
    have : Subsingleton (MonoidHom.id (Multiplicative ℤ)).ker :=
      ⟨fun a b => Subtype.ext (by
        have ha := MonoidHom.mem_ker.mp a.2
        have hb := MonoidHom.mem_ker.mp b.2
        exact ha.trans hb.symm)⟩
    exact cdLe_zero_of_subsingleton _
  exact cdLe_succ (MonoidHom.id _) (fun x => ⟨x, rfl⟩) lineTree h0

/-- The first projection `ℤ² → ℤ`. -/
def projFst : Multiplicative (ℤ × ℤ) →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (Multiplicative.toAdd x).1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The kernel of the first projection is `ℤ`. -/
def projFstKer : projFst.ker ≃* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (Multiplicative.toAdd x.1).2
  invFun m := ⟨Multiplicative.ofAdd (0, Multiplicative.toAdd m), by
    rw [MonoidHom.mem_ker]; rfl⟩
  left_inv x := by
    apply Subtype.ext
    have h : (Multiplicative.toAdd x.1).1 = 0 := by
      have := MonoidHom.mem_ker.mp x.2
      exact Multiplicative.toAdd.injective this |> fun h => by simpa [projFst] using congrArg Multiplicative.toAdd this
    show Multiplicative.ofAdd (0, (Multiplicative.toAdd x.1).2) = x.1
    apply Multiplicative.toAdd.injective
    ext <;> simp [h]
  right_inv m := rfl
  map_mul' x y := rfl

/-- `ℤ²` has cohomological dimension `≤ 2`. -/
theorem cdLe_int2 : CdLe k (Multiplicative (ℤ × ℤ)) 2 := by
  have h1 : CdLe k projFst.ker 1 := CdLe.of_mulEquiv projFstKer.symm cdLe_int
  exact cdLe_succ projFst (fun m => ⟨Multiplicative.ofAdd (Multiplicative.toAdd m, 0), rfl⟩) lineTree h1

end Dim
end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
