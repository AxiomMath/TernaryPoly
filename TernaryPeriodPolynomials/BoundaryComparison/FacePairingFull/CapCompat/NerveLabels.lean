module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.NerveCap
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeCap

@[expose] public section


/-!
# Labels of the model cone

For equivariant maps of `Γ`-sets `α : Z → Z'`, `β : Z → Z''` the three resolutions `ℚ[V^{•+1} × Z]`, `ℚ[V^{•+1} × Z']`,
`ℚ[V^{•+1} × Z'']` with the chain maps `prodMapHom α`, `prodMapHom β` form a labelled pushout cone: the label of the
cell `(x, z)` is `z`, faces and diagonal faces keep the label, and the maps send the cell `(x, z)` to `(x, α z)`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

section Model

variable (Γ : Type) [Group Γ] (V : Type) [MulAction Γ V] (Z Z' Z'' : Type)
  [MulAction Γ Z] [MulAction Γ Z'] [MulAction Γ Z'']
  (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1)
  (α : Z → Z') (hα : ∀ (γ : Γ) (z : Z), α (γ • z) = γ • α z)
  (β : Z → Z'') (hβ : ∀ (γ : Γ) (z : Z), β (γ • z) = γ • β z)

theorem nerveCells_cell (n : ℕ) (s : (Fin (n+1) → V) × Z) :
    (nerveCells Γ V Z hfree).cell n s = MonoidAlgebra.single s 1 := rfl

/-- The label of a cell of the model resolution. -/
def nerveLab (Y : Type) [MulAction Γ Y] (hY : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) (n : ℕ)
    (t : (nerveCells Γ V Y hY).S n) : Y :=
  (show (Fin (n+1) → V) × Y from t).2

theorem nerve_bd (Y : Type) [MulAction Γ Y] (hY : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) (n : ℕ)
    (s : (nerveCells Γ V Y hY).S (n+1)) :
    ((prodComplex Γ V Y).d (n+1) n).hom ((nerveCells Γ V Y hY).cell (n+1) s) ∈ Submodule.span ℚ
      {x | ∃ t : (nerveCells Γ V Y hY).S n, nerveLab Γ V Y hY n t = nerveLab Γ V Y hY (n+1) s ∧
        x = (nerveCells Γ V Y hY).cell n t} := by
  have h := d_single Γ V Y n (show (Fin (n+2) → V) × Y from s)
  have e : ((prodComplex Γ V Y).d (n+1) n).hom ((nerveCells Γ V Y hY).cell (n+1) s) =
      ∑ i : Fin (n+2), ((-1 : ℤ) ^ (i : ℕ)) • (MonoidAlgebra.single
        (face V Y i (show (Fin (n+2) → V) × Y from s)) (1 : ℚ) : (prodComplex Γ V Y).X n) :=
    (congrArg ((prodComplex Γ V Y).d (n+1) n).hom (nerveCells_cell Γ V Y hY (n+1) s)).trans h
  rw [e]
  refine Submodule.sum_mem _ (fun i _ => zsmul_mem (Submodule.subset_span ?_) _)
  exact ⟨face V Y i (show (Fin (n+2) → V) × Y from s), rfl, rfl⟩

/-- The labels of the model cone attached to `α` and `β`. -/
def nerveLabels :
    PushLabels (prodMapHom Γ V Z α hα) (prodMapHom Γ V Z β hβ) (nerveCells Γ V Z hfree)
      (nerveCells Γ V Z' hfree) (nerveCells Γ V Z'' hfree) Z Z' Z'' α β where
  φL_smul := hα
  φP_smul := hβ
  labA n s := nerveLab Γ V Z hfree n s
  labL n s := nerveLab Γ V Z' hfree n s
  labP n s := nerveLab Γ V Z'' hfree n s
  labA_smul _ _ _ := rfl
  labL_smul _ _ _ := rfl
  labP_smul _ _ _ := rfl
  bdA n s := nerve_bd Γ V Z hfree n s
  bdL n s := nerve_bd Γ V Z' hfree n s
  bdP n s := nerve_bd Γ V Z'' hfree n s
  aCell _ s := (s.1, α s.2)
  a_cell n s :=
    (congrArg ((prodMapHom Γ V Z α hα).f n).hom (nerveCells_cell Γ V Z hfree n s)).trans
      ((prodMapHom_f_single Γ V Z α hα n s.1 s.2).trans (nerveCells_cell Γ V Z' hfree n (s.1, α s.2)).symm)
  labL_aCell _ _ := rfl
  bCell _ s := (s.1, β s.2)
  b_cell n s :=
    (congrArg ((prodMapHom Γ V Z β hβ).f n).hom (nerveCells_cell Γ V Z hfree n s)).trans
      ((prodMapHom_f_single Γ V Z β hβ n s.1 s.2).trans (nerveCells_cell Γ V Z'' hfree n (s.1, β s.2)).symm)
  labP_bCell _ _ := rfl

theorem nerve_dg (Y : Type) [MulAction Γ Y] (hY : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) (p q n : ℕ)
    (h : p + q = n) (s : (nerveCells Γ V Y hY).S n) :
    (nerveDelta Γ V Y p q n h).hom ((nerveCells Γ V Y hY).cell n s) ∈ Submodule.span ℚ
      {x | ∃ (t' : (nerveCells Γ V Y hY).S p) (t : (nerveCells Γ V Y hY).S q),
        nerveLab Γ V Y hY q t = nerveLab Γ V Y hY n s ∧
        x = ((nerveCells Γ V Y hY).cell p t' ⊗ₜ[ℚ] (nerveCells Γ V Y hY).cell q t :
          ((prodComplex Γ V Y).X p ⊗ (prodComplex Γ V Y).X q : Rep.{0} ℚ Γ))} := by
  have e : (nerveDelta Γ V Y p q n h).hom ((nerveCells Γ V Y hY).cell n s) =
      ((nerveCells Γ V Y hY).cell p (frontFace V Y p n (by omega) (show (Fin (n+1) → V) × Y from s)) ⊗ₜ[ℚ]
        (nerveCells Γ V Y hY).cell q (backFace V Y p q n h (show (Fin (n+1) → V) × Y from s)) :
        ((prodComplex Γ V Y).X p ⊗ (prodComplex Γ V Y).X q : Rep.{0} ℚ Γ)) :=
    (congrArg (nerveDelta Γ V Y p q n h).hom (nerveCells_cell Γ V Y hY n s)).trans
      (nerveDelta_single Γ V Y p q n h (show (Fin (n+1) → V) × Y from s))
  rw [e]
  exact Submodule.subset_span ⟨_, _, rfl, rfl⟩

theorem nerve_strict :
    PushCone.Strict (a := prodMapHom Γ V Z α hα) (b := prodMapHom Γ V Z β hβ) (nerveDiagSystem Γ V Z)
      (nerveDiagSystem Γ V Z') (nerveDiagSystem Γ V Z'') where
  a_strict p q n h := nerveDelta_natural Γ V Z α hα p q n h
  b_strict p q n h := nerveDelta_natural Γ V Z β hβ p q n h
  a_eps := by
    refine hom_ext_single ((Fin (0 + 1) → V) × Z) _ (fun y => ?_)
    obtain ⟨x, z⟩ := y
    have e1 : ((prodMapHom Γ V Z α hα).f 0 ≫ nerveEps Γ V Z').hom (MonoidAlgebra.single (x, z) 1) =
        (nerveEps Γ V Z').hom (((prodMapHom Γ V Z α hα).f 0).hom (MonoidAlgebra.single (x, z) 1)) := rfl
    exact e1.trans ((congrArg (nerveEps Γ V Z').hom (prodMapHom_f_single Γ V Z α hα 0 x z)).trans
      ((nerveEps_single Γ V Z' (x, α z)).trans (nerveEps_single Γ V Z (x, z)).symm))
  b_eps := by
    refine hom_ext_single ((Fin (0 + 1) → V) × Z) _ (fun y => ?_)
    obtain ⟨x, z⟩ := y
    have e1 : ((prodMapHom Γ V Z β hβ).f 0 ≫ nerveEps Γ V Z'').hom (MonoidAlgebra.single (x, z) 1) =
        (nerveEps Γ V Z'').hom (((prodMapHom Γ V Z β hβ).f 0).hom (MonoidAlgebra.single (x, z) 1)) := rfl
    exact e1.trans ((congrArg (nerveEps Γ V Z'').hom (prodMapHom_f_single Γ V Z β hβ 0 x z)).trans
      ((nerveEps_single Γ V Z'' (x, β z)).trans (nerveEps_single Γ V Z (x, z)).symm))

theorem nerveLabels_diag :
    (nerveLabels Γ V Z Z' Z'' hfree α hα β hβ).Diag (nerveDiagSystem Γ V Z) (nerveDiagSystem Γ V Z')
      (nerveDiagSystem Γ V Z'') where
  dgA p q n h s := nerve_dg Γ V Z hfree p q n h s
  dgL p q n h s := nerve_dg Γ V Z' hfree p q n h s
  dgP p q n h s := nerve_dg Γ V Z'' hfree p q n h s

end Model

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
