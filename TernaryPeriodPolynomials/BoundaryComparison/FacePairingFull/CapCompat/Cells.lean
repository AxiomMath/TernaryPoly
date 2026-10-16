module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Engine
public import Mathlib.Algebra.Homology.HomologicalComplex

@[expose] public section


/-!
# Free `Γ`-cell bases of chain complexes of representations; carriers

A `CellBasis` of a chain complex `C` of representations of `Γ` presents each term `C.X n` as the permutation
representation `ℚ[S n]` of a free `Γ`-set of "cells".  Morphisms out of `C.X n` are the equivariant functions on
cells (`CellBasis.lift`).  A `CarrierData` attaches to each cell `s` a subcomplex `K s` of a target complex `D`
(permuted by `Γ` like the cells) such that the boundary of a cell is a combination of cells with smaller carriers.
`exists_sequence` is the recursion principle used for all constructions by equivariant acyclic carriers.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits
open TernaryPeriodPolynomials.Argument.TopHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

/-- A recursion principle: an infinite sequence of choices, each depending only on the previous one. -/
theorem exists_sequence (State : ℕ → Type) (I : State 0 → Prop)
    (R : ∀ m, State m → State (m+1) → Prop)
    (h0 : ∃ s : State 0, I s) (h : ∀ m (s : State m), ∃ s' : State (m+1), R m s s') :
    ∃ seq : ∀ m, State m, I (seq 0) ∧ ∀ m, R m (seq m) (seq (m+1)) := by
  obtain ⟨s0, hs0⟩ := h0
  choose step hstep using h
  let seq : ∀ m, State m := fun m => Nat.rec s0 (fun m s => step m s) m
  exact ⟨seq, hs0, fun m => hstep m (seq m)⟩

variable {Γ : Type} [Group Γ]

/-- A free `Γ`-basis of the terms of a chain complex of representations: each `C.X n` is the permutation
representation on a free `Γ`-set `S n` of cells, in the sense that equivariant functions on cells extend uniquely
to morphisms. -/
structure CellBasis (C : ChainComplex (Rep.{0} ℚ Γ) ℕ) where
  S : ℕ → Type
  act : ∀ n, MulAction Γ (S n)
  free : ∀ n (γ : Γ) (s : S n), @HSMul.hSMul Γ (S n) (S n) (@instHSMul Γ (S n) (act n).toSMul) γ s = s → γ = 1
  cell : ∀ n, S n → C.X n
  cell_smul : ∀ n (γ : Γ) (s : S n),
    cell n (@HSMul.hSMul Γ (S n) (S n) (@instHSMul Γ (S n) (act n).toSMul) γ s) = (C.X n).ρ γ (cell n s)
  lift : ∀ n {A : Rep.{0} ℚ Γ} (F : S n → A),
    (∀ (γ : Γ) (s : S n),
      F (@HSMul.hSMul Γ (S n) (S n) (@instHSMul Γ (S n) (act n).toSMul) γ s) = A.ρ γ (F s)) → (C.X n ⟶ A)
  lift_cell : ∀ n {A : Rep.{0} ℚ Γ} (F : S n → A)
    (hF : ∀ (γ : Γ) (s : S n),
      F (@HSMul.hSMul Γ (S n) (S n) (@instHSMul Γ (S n) (act n).toSMul) γ s) = A.ρ γ (F s)) (s : S n),
    (lift n F hF).hom (cell n s) = F s
  hom_ext : ∀ n {A : Rep.{0} ℚ Γ} {φ ψ : C.X n ⟶ A}, (∀ s, φ.hom (cell n s) = ψ.hom (cell n s)) → φ = ψ

attribute [instance] CellBasis.act

/-- A cell basis from isomorphisms with permutation representations. -/
def CellBasis.ofIso {C : ChainComplex (Rep.{0} ℚ Γ) ℕ} (S : ℕ → Type) [∀ n, MulAction Γ (S n)]
    (free : ∀ n (γ : Γ) (s : S n), γ • s = s → γ = 1)
    (iso : ∀ n, Rep.ofMulAction ℚ Γ (S n) ≅ C.X n) : CellBasis C where
  S := S
  act := inferInstance
  free := free
  cell n s := (iso n).hom.hom (MonoidAlgebra.single s 1)
  cell_smul n γ s := by
    have := Rep.hom_comm_apply (iso n).hom γ (MonoidAlgebra.single s 1)
    simpa [Representation.ofMulAction_single] using this
  lift n {A} F hF := (iso n).inv ≫ ofMulActionLift (S n) A F hF
  lift_cell n {A} F hF s := by
    have h1 : ((iso n).inv ≫ ofMulActionLift (S n) A F hF).hom ((iso n).hom.hom (MonoidAlgebra.single s 1)) =
        ((iso n).hom ≫ ((iso n).inv ≫ ofMulActionLift (S n) A F hF)).hom (MonoidAlgebra.single s 1) := rfl
    rw [h1, Iso.hom_inv_id_assoc]
    exact ofMulActionLift_single _ _ _ _ s
  hom_ext n {A} φ ψ h := by
    have : (iso n).hom ≫ φ = (iso n).hom ≫ ψ := hom_ext_single (S n) A h
    exact (cancel_epi _).mp this

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
