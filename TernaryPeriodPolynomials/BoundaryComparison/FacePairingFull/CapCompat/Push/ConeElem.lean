module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeCells

@[expose] public section


/-!
# Elementwise calculus in a pushout cone

Projections onto the coordinates of a pushout cone, the differential on coordinate elements, and the augmentation.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]
  {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}

namespace PushCone

variable (𝒞 : PushCone A L P K a b)

/-- Projection of a positive-degree term onto its shifted `A` coordinate. -/
def pA (n : ℕ) : K.X (n+1) ⟶ A.X n := 𝒞.desc n (𝟙 _) 0 0
def pL (n : ℕ) : K.X (n+1) ⟶ L.X (n+1) := 𝒞.desc n 0 (𝟙 _) 0
def pP (n : ℕ) : K.X (n+1) ⟶ P.X (n+1) := 𝒞.desc n 0 0 (𝟙 _)
def pL0 : K.X 0 ⟶ L.X 0 := 𝒞.desc0 (𝟙 _) 0
def pP0 : K.X 0 ⟶ P.X 0 := 𝒞.desc0 0 (𝟙 _)

theorem pA_iA (n : ℕ) (x : A.X n) : (𝒞.pA n).hom ((𝒞.iA n).hom x) = x := by
  have := congrArg (fun φ => φ.hom x) (𝒞.iA_desc n (𝟙 (A.X n)) (0 : L.X (n+1) ⟶ A.X n) (0 : P.X (n+1) ⟶ A.X n))
  unfold pA
  simpa using this

theorem pA_iL (n : ℕ) (l : L.X (n+1)) : (𝒞.pA n).hom ((𝒞.iL (n+1)).hom l) = 0 := by
  have := congrArg (fun φ => φ.hom l) (𝒞.iL_desc n (𝟙 (A.X n)) (0 : L.X (n+1) ⟶ A.X n) (0 : P.X (n+1) ⟶ A.X n))
  unfold pA
  simpa using this

theorem pA_iP (n : ℕ) (p : P.X (n+1)) : (𝒞.pA n).hom ((𝒞.iP (n+1)).hom p) = 0 := by
  have := congrArg (fun φ => φ.hom p) (𝒞.iP_desc n (𝟙 (A.X n)) (0 : L.X (n+1) ⟶ A.X n) (0 : P.X (n+1) ⟶ A.X n))
  unfold pA
  simpa using this

theorem pL_iA (n : ℕ) (x : A.X n) : (𝒞.pL n).hom ((𝒞.iA n).hom x) = 0 := by
  have := congrArg (fun φ => φ.hom x) (𝒞.iA_desc n (0 : A.X n ⟶ L.X (n+1)) (𝟙 (L.X (n+1))) (0 : P.X (n+1) ⟶ L.X (n+1)))
  unfold pL
  simpa using this

theorem pL_iL (n : ℕ) (l : L.X (n+1)) : (𝒞.pL n).hom ((𝒞.iL (n+1)).hom l) = l := by
  have := congrArg (fun φ => φ.hom l) (𝒞.iL_desc n (0 : A.X n ⟶ L.X (n+1)) (𝟙 (L.X (n+1))) (0 : P.X (n+1) ⟶ L.X (n+1)))
  unfold pL
  simpa using this

theorem pL_iP (n : ℕ) (p : P.X (n+1)) : (𝒞.pL n).hom ((𝒞.iP (n+1)).hom p) = 0 := by
  have := congrArg (fun φ => φ.hom p) (𝒞.iP_desc n (0 : A.X n ⟶ L.X (n+1)) (𝟙 (L.X (n+1))) (0 : P.X (n+1) ⟶ L.X (n+1)))
  unfold pL
  simpa using this

theorem pP_iA (n : ℕ) (x : A.X n) : (𝒞.pP n).hom ((𝒞.iA n).hom x) = 0 := by
  have := congrArg (fun φ => φ.hom x) (𝒞.iA_desc n (0 : A.X n ⟶ P.X (n+1)) (0 : L.X (n+1) ⟶ P.X (n+1)) (𝟙 (P.X (n+1))))
  unfold pP
  simpa using this

theorem pP_iL (n : ℕ) (l : L.X (n+1)) : (𝒞.pP n).hom ((𝒞.iL (n+1)).hom l) = 0 := by
  have := congrArg (fun φ => φ.hom l) (𝒞.iL_desc n (0 : A.X n ⟶ P.X (n+1)) (0 : L.X (n+1) ⟶ P.X (n+1)) (𝟙 (P.X (n+1))))
  unfold pP
  simpa using this

theorem pP_iP (n : ℕ) (p : P.X (n+1)) : (𝒞.pP n).hom ((𝒞.iP (n+1)).hom p) = p := by
  have := congrArg (fun φ => φ.hom p) (𝒞.iP_desc n (0 : A.X n ⟶ P.X (n+1)) (0 : L.X (n+1) ⟶ P.X (n+1)) (𝟙 (P.X (n+1))))
  unfold pP
  simpa using this

end PushCone

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
