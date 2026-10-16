module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.ConePairing

@[expose] public section


/-!
# The corner chain of a coinvariant cycle of a homotopy pushout cone

Formalized by Claude Sonnet 5.5.

For a coinvariant cycle `v` of the cone `K` of `a : A ⟶ L`, `b : A ⟶ P` with `v = i_A x + i_L l + i_P p`, the corner chain `x = p_A v` is a
coinvariant 3-cycle of `A`, and its images `a x`, `b x` are coinvariant boundaries in `L`, `P` (they pair to zero with every cocycle of `L`, `P`).
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]
  {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}

namespace PushCone

variable (𝒞 : PushCone A L P K a b)

/-- The boundary of the corner chain of a coinvariant cycle vanishes in the coinvariants. -/
theorem corner_cycle {v : K.X 4} (hv : IsCoinvCycle v) (φ : A.X 2 ⟶ 𝟙_ (Rep.{0} ℚ Γ)) :
    φ.hom ((A.d 3 2).hom ((𝒞.pA 3).hom v)) = 0 := by
  have hdec := 𝒞.decomp_succ 3 v
  generalize (𝒞.pA 3).hom v = x at hdec ⊢
  generalize (𝒞.pL 3).hom v = l at hdec
  generalize (𝒞.pP 3).hom v = p at hdec
  subst hdec
  have hd : (K.d 4 3).hom ((𝒞.iA 3).hom x + (𝒞.iL 4).hom l + (𝒞.iP 4).hom p) =
      (-(𝒞.iA 2).hom ((A.d 3 2).hom x) + (𝒞.iL 3).hom ((a.f 3).hom x) - (𝒞.iP 3).hom ((b.f 3).hom x)) +
        (𝒞.iL 3).hom ((L.d 4 3).hom l) + (𝒞.iP 3).hom ((P.d 4 3).hom p) := by
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (𝒞.d_iA_succ 2 x) (𝒞.d_iL 3 l)) (𝒞.d_iP 3 p)
  have c : φ.hom ((𝒞.pA 2).hom ((K.d 4 3).hom ((𝒞.iA 3).hom x + (𝒞.iL 4).hom l + (𝒞.iP 4).hom p))) = 0 :=
    hv (𝒞.pA 2 ≫ φ)
  rw [hd] at c
  simp only [map_add, map_sub, map_neg, 𝒞.pA_iA, 𝒞.pA_iL, 𝒞.pA_iP, add_zero, sub_zero] at c
  simpa using c

/-- The image of the corner chain in `L` pairs to zero with every cocycle of `L`. -/
theorem corner_line {v : K.X 4} (hv : IsCoinvCycle v) (ψ : L.X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ)) (hψ : L.d 4 3 ≫ ψ = 0) :
    ψ.hom ((a.f 3).hom ((𝒞.pA 3).hom v)) = 0 := by
  have hdec := 𝒞.decomp_succ 3 v
  generalize (𝒞.pA 3).hom v = x at hdec ⊢
  generalize (𝒞.pL 3).hom v = l at hdec
  generalize (𝒞.pP 3).hom v = p at hdec
  subst hdec
  have hd : (K.d 4 3).hom ((𝒞.iA 3).hom x + (𝒞.iL 4).hom l + (𝒞.iP 4).hom p) =
      (-(𝒞.iA 2).hom ((A.d 3 2).hom x) + (𝒞.iL 3).hom ((a.f 3).hom x) - (𝒞.iP 3).hom ((b.f 3).hom x)) +
        (𝒞.iL 3).hom ((L.d 4 3).hom l) + (𝒞.iP 3).hom ((P.d 4 3).hom p) := by
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (𝒞.d_iA_succ 2 x) (𝒞.d_iL 3 l)) (𝒞.d_iP 3 p)
  have c : ψ.hom ((𝒞.pL 2).hom ((K.d 4 3).hom ((𝒞.iA 3).hom x + (𝒞.iL 4).hom l + (𝒞.iP 4).hom p))) = 0 :=
    hv (𝒞.pL 2 ≫ ψ)
  rw [hd] at c
  simp only [map_add, map_sub, map_neg, 𝒞.pL_iA, 𝒞.pL_iL, 𝒞.pL_iP, neg_zero, zero_add, add_zero, sub_zero] at c
  have h0 : ψ.hom ((L.d 4 3).hom l) = 0 := congrArg (fun m => m.hom l) hψ
  rw [h0, add_zero] at c
  exact c

/-- The image of the corner chain in `P` pairs to zero with every cocycle of `P`. -/
theorem corner_plane {v : K.X 4} (hv : IsCoinvCycle v) (ψ : P.X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ)) (hψ : P.d 4 3 ≫ ψ = 0) :
    ψ.hom ((b.f 3).hom ((𝒞.pA 3).hom v)) = 0 := by
  have hdec := 𝒞.decomp_succ 3 v
  generalize (𝒞.pA 3).hom v = x at hdec ⊢
  generalize (𝒞.pL 3).hom v = l at hdec
  generalize (𝒞.pP 3).hom v = p at hdec
  subst hdec
  have hd : (K.d 4 3).hom ((𝒞.iA 3).hom x + (𝒞.iL 4).hom l + (𝒞.iP 4).hom p) =
      (-(𝒞.iA 2).hom ((A.d 3 2).hom x) + (𝒞.iL 3).hom ((a.f 3).hom x) - (𝒞.iP 3).hom ((b.f 3).hom x)) +
        (𝒞.iL 3).hom ((L.d 4 3).hom l) + (𝒞.iP 3).hom ((P.d 4 3).hom p) := by
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (𝒞.d_iA_succ 2 x) (𝒞.d_iL 3 l)) (𝒞.d_iP 3 p)
  have c : ψ.hom ((𝒞.pP 2).hom ((K.d 4 3).hom ((𝒞.iA 3).hom x + (𝒞.iL 4).hom l + (𝒞.iP 4).hom p))) = 0 :=
    hv (𝒞.pP 2 ≫ ψ)
  rw [hd] at c
  simp only [map_add, map_sub, map_neg, 𝒞.pP_iA, 𝒞.pP_iL, 𝒞.pP_iP, neg_zero, add_zero, zero_sub] at c
  have h0 : ψ.hom ((P.d 4 3).hom p) = 0 := congrArg (fun m => m.hom p) hψ
  rw [h0, add_zero] at c
  have := neg_eq_zero.mp c
  exact this

end PushCone

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
