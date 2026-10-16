module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.EichlerPrim
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.BinCoeff

@[expose] public section


open MvPolynomial Matrix CategoryTheory groupCohomology
open scoped MatrixGroups

/-!
# Assembly of the Eichler–Shimura route: period identification

`periodPrim f g = P_f + P̄_g` (holomorphic Eichler primitive of `f` plus the antiholomorphic
primitive of `g`, in coefficient coordinates) transforms by the period cocycles of `ESSpan`
(`periodPrim_mob`). Consequently, if a function `Φ₀` transforming by a cocycle `c₀` cohomologous to
`c` agrees with `periodPrim f g` up to a constant on `U`, the class of `c` lies in the span of the
holomorphic and antiholomorphic period classes (`mem_span_of_periods`).

This is the last step of the Assembly plan. The unconditional
spanning theorem additionally needs the harmonic representative `Φ₀` and the approximants from the
L² Hodge step (H, `L2Forms`); nothing here assumes them.

Written by Claude Opus 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.Assembly

open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ESFoundations
open TernaryPeriodPolynomials.Argument.ESFoundations.BinCoeff
open TernaryPeriodPolynomials.Argument.ESFoundations.EichlerPrim
open TernaryPeriodPolynomials.Argument.ESFoundations.SymFrame
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)

variable {Λ : Subgroup SL(2, ℤ)} {n : ℕ}

/-- The Eichler primitive of `f` plus the antiholomorphic primitive of `g`, in `Wn n`. -/
def periodPrim (f g : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) (z : ℂ) : Wn n :=
  (EuclideanSpace.equiv (Fin (n + 1 + 1)) ℂ).symm (eichPrim f z + antiPrim g z)

theorem periodPrim_mob (f g : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) (δ : Λ) {z : ℂ}
    (hz : 0 < z.im) :
    periodPrim f g (Partition.mob δ z) =
      Matrix.toEuclideanLin (rhoW Λ n δ) (periodPrim f g z) +
        (cocycleW (holCocycle f) δ + cocycleW (antiholCocycle g) δ) := by
  rw [periodPrim, eichPrim_mob f δ hz, antiPrim_mob g δ hz]
  apply (EuclideanSpace.equiv (Fin (n + 1 + 1)) ℂ).injective
  funext i
  simp only [ContinuousLinearEquiv.apply_symm_apply, Pi.add_apply]
  change _ = (rhoW Λ n δ *ᵥ (eichPrim f z + antiPrim g z)) i + (coords (n + 1) (eichlerForm f δ.1).1 i +
    coords (n + 1) (MvPolynomial.map (starRingEnd ℂ) (eichlerForm g δ.1).1) i)
  rw [mulVec_add]
  simp only [Pi.add_apply]
  have hr : rhoW Λ n δ = symRep (n + 1) δ := rfl
  rw [hr]
  ring


theorem cocycleW_sub (a b : cocycles₁ (binRep Λ n)) (δ : Λ) :
    cocycleW (a - b) δ = cocycleW a δ - cocycleW b δ := toW_sub _ _

theorem cocycleW_add (a b : cocycles₁ (binRep Λ n)) (δ : Λ) :
    cocycleW (a + b) δ = cocycleW a δ + cocycleW b δ := toW_add _ _

/-- **Periods of a harmonic representative.** If `Φ₀` transforms by `c₀`, `c` is cohomologous
to `c₀`, and `Φ₀` is the period primitive of `f` (holomorphic) and `g` (antiholomorphic) up to a
constant, then the class of `c` lies in the span of the holomorphic and antiholomorphic period
classes. -/
theorem mem_span_of_periods (c : cocycles₁ (binRep Λ n))
    (f g : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) (Φ₀ : ℂ → Wn n) (c₀ : Λ → Wn n)
    (hΦ₀ : ∀ δ : Λ, ∀ z ∈ U,
      Φ₀ (Partition.mob δ z) = Matrix.toEuclideanLin (rhoW Λ n δ) (Φ₀ z) + c₀ δ)
    (hcob : ∃ w : Wn n, ∀ δ : Λ, cocycleW c δ - c₀ δ = Matrix.toEuclideanLin (rhoW Λ n δ) w - w)
    (hconst : ∃ K : Wn n, ∀ z ∈ U, Φ₀ z = periodPrim f g z + K) :
    H1π (binRep Λ n) c ∈ Submodule.span ℂ
      (Set.range (fun f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ) =>
        H1π (binRep Λ n) (holCocycle f)) ∪
      Set.range (fun f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ) =>
        H1π (binRep Λ n) (antiholCocycle f))) := by
  obtain ⟨w, hw⟩ := hcob
  obtain ⟨K, hK⟩ := hconst
  have hI : Complex.I ∈ U := by show 0 < Complex.I.im; simp
  have hc₀ : ∀ δ : Λ, c₀ δ = cocycleW (holCocycle f) δ + cocycleW (antiholCocycle g) δ +
      (K - Matrix.toEuclideanLin (rhoW Λ n δ) K) := by
    intro δ
    have h1 := hΦ₀ δ Complex.I hI
    rw [hK _ (Partition.mob_mem _ _), hK _ hI, periodPrim_mob f g δ (by simp), map_add] at h1
    have : c₀ δ = Matrix.toEuclideanLin (rhoW Λ n δ) (periodPrim f g Complex.I) +
        (cocycleW (holCocycle f) δ + cocycleW (antiholCocycle g) δ) + K -
        (Matrix.toEuclideanLin (rhoW Λ n δ) (periodPrim f g Complex.I) +
          Matrix.toEuclideanLin (rhoW Λ n δ) K) := by
      rw [h1]; abel
    rw [this]; abel
  set d : cocycles₁ (binRep Λ n) := c - (holCocycle f + antiholCocycle g) with hd
  have hd0 : H1π (binRep Λ n) d = 0 := by
    refine H1π_eq_zero_of_coboundaryW d (w - K) fun δ => ?_
    rw [hd, cocycleW_sub, cocycleW_add, map_sub]
    have := hw δ
    rw [hc₀ δ] at this
    rw [show cocycleW c δ = cocycleW (holCocycle f) δ + cocycleW (antiholCocycle g) δ +
      (K - Matrix.toEuclideanLin (rhoW Λ n δ) K) + (Matrix.toEuclideanLin (rhoW Λ n δ) w - w) by
        rw [← this]; abel]
    abel
  have hsum : H1π (binRep Λ n) c =
      H1π (binRep Λ n) (holCocycle f) + H1π (binRep Λ n) (antiholCocycle g) := by
    have : H1π (binRep Λ n) d = H1π (binRep Λ n) c -
        (H1π (binRep Λ n) (holCocycle f) + H1π (binRep Λ n) (antiholCocycle g)) := by
      rw [hd, map_sub, map_add]
    rw [hd0] at this
    exact sub_eq_zero.mp this.symm
  rw [hsum]
  exact Submodule.add_mem _ (Submodule.subset_span (Or.inl ⟨f, rfl⟩))
    (Submodule.subset_span (Or.inr ⟨g, rfl⟩))


/-- The `ℝ`-linear map `v ↦ v·a + v̄·b` on `ℂ`. -/
def wirt (a b : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.smulRight (1 : ℂ →L[ℝ] ℂ) a) +
    ContinuousLinearMap.smulRight Complex.conjCLE.toContinuousLinearMap b

theorem wirt_apply (a b v : ℂ) : wirt a b v = v * a + starRingEnd ℂ v * b := by
  simp [wirt, smul_eq_mul]

theorem hasFDerivAt_eichPrim_coord (f : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) {z : ℂ}
    (hz : 0 < z.im) (i : Fin (n + 1 + 1)) :
    HasFDerivAt (fun w => eichPrim f w i)
      (wirt ((TernaryPeriodPolynomials.Argument.SeedC3.cuspH (LamGL Λ) n f z •
        coords (n + 1) ((C z * X 1 - X 0) ^ (n + 1) : MvPolynomial (Fin 2) ℂ)) i) 0) z := by
  have h := ((hasDerivAt_pi.mp (hasDerivAt_eichPrim f hz)) i).hasFDerivAt.restrictScalars ℝ
  refine h.congr_fderiv ?_
  ext1 v
  rw [wirt_apply]
  simp

theorem hasFDerivAt_antiPrim_coord (g : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) {z : ℂ}
    (hz : 0 < z.im) (i : Fin (n + 1 + 1)) :
    HasFDerivAt (fun w => antiPrim g w i)
      (wirt 0 (starRingEnd ℂ ((TernaryPeriodPolynomials.Argument.SeedC3.cuspH (LamGL Λ) n g z •
        coords (n + 1) ((C z * X 1 - X 0) ^ (n + 1) : MvPolynomial (Fin 2) ℂ)) i))) z := by
  have h := ((hasDerivAt_pi.mp (hasDerivAt_eichPrim g hz)) i).hasFDerivAt.restrictScalars ℝ
  have h2 := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z h
  refine h2.congr_fderiv ?_
  ext1 v
  rw [wirt_apply]
  simp [map_mul, mul_comm]


/-- **Matching derivatives give the period primitive up to a constant.** If `Φ₀` has Wirtinger
derivative `(α, β)` on `U` with `α = f·(zX₁ - X₀)^{n+1}` and `β = conj(g·(zX₁ - X₀)^{n+1})` in
coefficient coordinates, then `Φ₀ = periodPrim f g + K` on `U`. -/
theorem eq_periodPrim_add_const (f g : CuspForm (LamGL Λ) ((n + 3 : ℕ) : ℤ)) (Φ₀ α β : ℂ → Wn n)
    (hΦ : ∀ z ∈ U, ∃ L : ℂ →L[ℝ] Wn n, HasFDerivAt Φ₀ L z ∧
      ∀ v, L v = v • α z + (starRingEnd ℂ v) • β z)
    (hα : ∀ z ∈ U, ∀ i, α z i = (TernaryPeriodPolynomials.Argument.SeedC3.cuspH (LamGL Λ) n f z •
        coords (n + 1) ((C z * X 1 - X 0) ^ (n + 1) : MvPolynomial (Fin 2) ℂ)) i)
    (hβ : ∀ z ∈ U, ∀ i, β z i = starRingEnd ℂ
        ((TernaryPeriodPolynomials.Argument.SeedC3.cuspH (LamGL Λ) n g z •
          coords (n + 1) ((C z * X 1 - X 0) ^ (n + 1) : MvPolynomial (Fin 2) ℂ)) i)) :
    ∃ K : Wn n, ∀ z ∈ U, Φ₀ z = periodPrim f g z + K := by
  have hpre : IsPreconnected U := (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  have hI : Complex.I ∈ U := by show 0 < Complex.I.im; simp
  have hcoord : ∀ i : Fin (n + 1 + 1), ∀ z ∈ U,
      Φ₀ z i - (eichPrim f z i + antiPrim g z i) =
        Φ₀ Complex.I i - (eichPrim f Complex.I i + antiPrim g Complex.I i) := by
    intro i z hz
    have hd : ∀ w ∈ U, HasFDerivAt
        (fun w => Φ₀ w i - (eichPrim f w i + antiPrim g w i)) (0 : ℂ →L[ℝ] ℂ) w := by
      intro w hw
      obtain ⟨L, hL, hLv⟩ := hΦ w hw
      have hp := ((EuclideanSpace.proj i : Wn n →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp w hL
      have he := hasFDerivAt_eichPrim_coord f hw i
      have ha := hasFDerivAt_antiPrim_coord g hw i
      refine ((hp.sub (he.add ha))).congr_fderiv ?_
      ext1 v
      simp only [_root_.sub_apply, _root_.add_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', hLv,
        wirt_apply, _root_.zero_apply]
      simp [hα w hw i, hβ w hw i]
    exact isOpen_U.is_const_of_fderiv_eq_zero hpre
      (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hd w hw).fderiv) hz hI
  refine ⟨Φ₀ Complex.I - periodPrim f g Complex.I, fun z hz => ?_⟩
  apply (EuclideanSpace.equiv (Fin (n + 1 + 1)) ℂ).injective
  funext i
  have := hcoord i z hz
  simp only [periodPrim, map_add, map_sub, ContinuousLinearEquiv.apply_symm_apply, Pi.add_apply,
    Pi.sub_apply] at this ⊢
  change Φ₀ z i = eichPrim f z i + antiPrim g z i +
    (Φ₀ Complex.I i - (eichPrim f Complex.I i + antiPrim g Complex.I i))
  rw [← this]
  ring

end TernaryPeriodPolynomials.Argument.ESFoundations.Assembly
