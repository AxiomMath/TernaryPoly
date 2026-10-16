module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeLeibniz
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Cells
public import Mathlib.Algebra.Group.Action.Sum

@[expose] public section


/-!
# The free cell basis of a pushout cone

If `A`, `L`, `P` have free `Γ`-cell bases, then so does the homotopy pushout cone `K` (in the coordinate presentation
`PushCone`): the cells of `K` in degree `n+1` are the cells of `A` in degree `n` (shifted), of `L` and of `P` in degree
`n+1`; in degree `0` those of `L` and `P`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]
  {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}

namespace PushCone

variable (BA : CellBasis A) (BL : CellBasis L) (BP : CellBasis P)

/-- The type of cells of the pushout cone in degree `n`. -/
def coneS : ℕ → Type
  | 0 => BL.S 0 ⊕ BP.S 0
  | n+1 => BA.S n ⊕ (BL.S (n+1) ⊕ BP.S (n+1))

@[instance_reducible]
def coneAct : ∀ n, MulAction Γ (coneS BA BL BP n)
  | 0 => inferInstanceAs (MulAction Γ (BL.S 0 ⊕ BP.S 0))
  | n+1 => inferInstanceAs (MulAction Γ (BA.S n ⊕ (BL.S (n+1) ⊕ BP.S (n+1))))

attribute [instance] coneAct

variable (𝒞 : PushCone A L P K a b)

/-- The cell of the pushout cone attached to a cell of a stratum. -/
def coneCell : ∀ n, coneS BA BL BP n → K.X n
  | 0, Sum.inl s => (𝒞.iL 0).hom (BL.cell 0 s)
  | 0, Sum.inr s => (𝒞.iP 0).hom (BP.cell 0 s)
  | n+1, Sum.inl s => (𝒞.iA n).hom (BA.cell n s)
  | n+1, Sum.inr (Sum.inl s) => (𝒞.iL (n+1)).hom (BL.cell (n+1) s)
  | n+1, Sum.inr (Sum.inr s) => (𝒞.iP (n+1)).hom (BP.cell (n+1) s)

theorem coneCell_smul (n : ℕ) (γ : Γ) (s : coneS BA BL BP n) :
    coneCell BA BL BP 𝒞 n (γ • s) = (K.X n).ρ γ (coneCell BA BL BP 𝒞 n s) := by
  cases n with
  | zero =>
    rcases s with s | s
    · change (𝒞.iL 0).hom (BL.cell 0 (γ • s)) = _
      rw [BL.cell_smul]; exact Rep.hom_comm_apply (𝒞.iL 0) γ _
    · change (𝒞.iP 0).hom (BP.cell 0 (γ • s)) = _
      rw [BP.cell_smul]; exact Rep.hom_comm_apply (𝒞.iP 0) γ _
  | succ n =>
    rcases s with s | s | s
    · change (𝒞.iA n).hom (BA.cell n (γ • s)) = _
      rw [BA.cell_smul]; exact Rep.hom_comm_apply (𝒞.iA n) γ _
    · change (𝒞.iL (n+1)).hom (BL.cell (n+1) (γ • s)) = _
      rw [BL.cell_smul]; exact Rep.hom_comm_apply (𝒞.iL (n+1)) γ _
    · change (𝒞.iP (n+1)).hom (BP.cell (n+1) (γ • s)) = _
      rw [BP.cell_smul]; exact Rep.hom_comm_apply (𝒞.iP (n+1)) γ _

theorem coneS_free (n : ℕ) (γ : Γ) (s : coneS BA BL BP n) (h : γ • s = s) : γ = 1 := by
  cases n with
  | zero =>
    rcases s with s | s
    · exact BL.free 0 γ s (Sum.inl.inj h)
    · exact BP.free 0 γ s (Sum.inr.inj h)
  | succ n =>
    rcases s with s | s | s
    · exact BA.free n γ s (Sum.inl.inj h)
    · exact BL.free (n+1) γ s (Sum.inl.inj (Sum.inr.inj h))
    · exact BP.free (n+1) γ s (Sum.inr.inj (Sum.inr.inj h))

/-- The morphism out of a cone term attached to an equivariant function on cells. -/
def coneLift : ∀ (n : ℕ) {Z : Rep.{0} ℚ Γ} (F : coneS BA BL BP n → Z),
    (∀ (γ : Γ) (s : coneS BA BL BP n), F (γ • s) = Z.ρ γ (F s)) → (K.X n ⟶ Z)
  | 0, _, F, hF => 𝒞.desc0 (BL.lift 0 (fun s => F (Sum.inl s)) (fun γ s => hF γ (Sum.inl s)))
      (BP.lift 0 (fun s => F (Sum.inr s)) (fun γ s => hF γ (Sum.inr s)))
  | n+1, _, F, hF => 𝒞.desc n (BA.lift n (fun s => F (Sum.inl s)) (fun γ s => hF γ (Sum.inl s)))
      (BL.lift (n+1) (fun s => F (Sum.inr (Sum.inl s))) (fun γ s => hF γ (Sum.inr (Sum.inl s))))
      (BP.lift (n+1) (fun s => F (Sum.inr (Sum.inr s))) (fun γ s => hF γ (Sum.inr (Sum.inr s))))

theorem coneLift_cell (n : ℕ) {Z : Rep.{0} ℚ Γ} (F : coneS BA BL BP n → Z)
    (hF : ∀ (γ : Γ) (s : coneS BA BL BP n), F (γ • s) = Z.ρ γ (F s)) (s : coneS BA BL BP n) :
    (coneLift BA BL BP 𝒞 n F hF).hom (coneCell BA BL BP 𝒞 n s) = F s := by
  cases n with
  | zero =>
    rcases s with s | s
    · have := congrArg (fun φ => φ.hom (BL.cell 0 s))
        (𝒞.iL0_desc0 (BL.lift 0 (fun s => F (Sum.inl s)) (fun γ s => hF γ (Sum.inl s)))
          (BP.lift 0 (fun s => F (Sum.inr s)) (fun γ s => hF γ (Sum.inr s))))
      exact this.trans (BL.lift_cell 0 _ _ s)
    · have := congrArg (fun φ => φ.hom (BP.cell 0 s))
        (𝒞.iP0_desc0 (BL.lift 0 (fun s => F (Sum.inl s)) (fun γ s => hF γ (Sum.inl s)))
          (BP.lift 0 (fun s => F (Sum.inr s)) (fun γ s => hF γ (Sum.inr s))))
      exact this.trans (BP.lift_cell 0 _ _ s)
  | succ n =>
    rcases s with s | s | s
    · have := congrArg (fun φ => φ.hom (BA.cell n s))
        (𝒞.iA_desc n (BA.lift n (fun s => F (Sum.inl s)) (fun γ s => hF γ (Sum.inl s)))
          (BL.lift (n+1) (fun s => F (Sum.inr (Sum.inl s))) (fun γ s => hF γ (Sum.inr (Sum.inl s))))
          (BP.lift (n+1) (fun s => F (Sum.inr (Sum.inr s))) (fun γ s => hF γ (Sum.inr (Sum.inr s)))))
      exact this.trans (BA.lift_cell n _ _ s)
    · have := congrArg (fun φ => φ.hom (BL.cell (n+1) s))
        (𝒞.iL_desc n (BA.lift n (fun s => F (Sum.inl s)) (fun γ s => hF γ (Sum.inl s)))
          (BL.lift (n+1) (fun s => F (Sum.inr (Sum.inl s))) (fun γ s => hF γ (Sum.inr (Sum.inl s))))
          (BP.lift (n+1) (fun s => F (Sum.inr (Sum.inr s))) (fun γ s => hF γ (Sum.inr (Sum.inr s)))))
      exact this.trans (BL.lift_cell (n+1) _ _ s)
    · have := congrArg (fun φ => φ.hom (BP.cell (n+1) s))
        (𝒞.iP_desc n (BA.lift n (fun s => F (Sum.inl s)) (fun γ s => hF γ (Sum.inl s)))
          (BL.lift (n+1) (fun s => F (Sum.inr (Sum.inl s))) (fun γ s => hF γ (Sum.inr (Sum.inl s))))
          (BP.lift (n+1) (fun s => F (Sum.inr (Sum.inr s))) (fun γ s => hF γ (Sum.inr (Sum.inr s)))))
      exact this.trans (BP.lift_cell (n+1) _ _ s)

theorem cone_hom_ext (n : ℕ) {Z : Rep.{0} ℚ Γ} {φ ψ : K.X n ⟶ Z}
    (h : ∀ s, φ.hom (coneCell BA BL BP 𝒞 n s) = ψ.hom (coneCell BA BL BP 𝒞 n s)) : φ = ψ := by
  cases n with
  | zero =>
    apply 𝒞.ext0
    · exact BL.hom_ext 0 (fun s => h (Sum.inl s))
    · exact BP.hom_ext 0 (fun s => h (Sum.inr s))
  | succ n =>
    apply 𝒞.ext n
    · exact BA.hom_ext n (fun s => h (Sum.inl s))
    · exact BL.hom_ext (n+1) (fun s => h (Sum.inr (Sum.inl s)))
    · exact BP.hom_ext (n+1) (fun s => h (Sum.inr (Sum.inr s)))

/-- The free cell basis of the pushout cone. -/
def coneCells : CellBasis K where
  S := coneS BA BL BP
  act := coneAct BA BL BP
  free := coneS_free BA BL BP
  cell := coneCell BA BL BP 𝒞
  cell_smul := coneCell_smul BA BL BP 𝒞
  lift := fun n {_} F hF => coneLift BA BL BP 𝒞 n F hF
  lift_cell := fun n {_} F hF s => coneLift_cell BA BL BP 𝒞 n F hF s
  hom_ext := fun n {_} _ _ h => cone_hom_ext BA BL BP 𝒞 n h

end PushCone

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
