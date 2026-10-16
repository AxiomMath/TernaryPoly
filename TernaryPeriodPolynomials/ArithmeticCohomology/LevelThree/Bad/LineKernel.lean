module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineKappa
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineModel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Lattice.TwoCocycleDetection

@[expose] public section


/-!
# Vanishing of `H²` of the bad-line radical

The upper line radical `U ≅ ℤ²` acts on `Sym^n` through `exp(-N₀), exp(-N₁)` with
`N_i = X_{i+1} ∂_{X₀}` (`radicalInfinitesimal`). The kernel of `κ = coeff_{X₀ⁿ}` is `N₀V + N₁V`
(`mem_Wsp_of_kappaB`), so a two-cocycle of `U` is a coboundary as soon as `κ` kills its alternation
(`radical_H2_zero`). For a two-cocycle `c` of `ΛB`, the restriction to `U` gives such a cocycle
(`radG`), and the radical restriction of the class of `c` vanishes when
`κ(c(Ux e₁, Ux e₂) - c(Ux e₂, Ux e₁)) = 0` (`radicalRestriction_zero`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.BadLineKernel

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open LineCoordinates IdentityPlaneCosets LevelOneCosets LevelThreeCosets BadLineCoordinates
open BadLineCosets BadLineTransitions BadLineEdge BadLineKappa BadLineModel
open GoodLineRestriction (deg3)
open LocalHecke AmbientHecke IdentityPlaneCoordinate

variable (n : ℕ)

/-- The monomial `c X^m` as an element of `Sym^n`, for `|m| = n`. -/
def monoHP (m : Fin 3 →₀ ℕ) (c : ℂ) (h : m 0 + m 1 + m 2 = n) : HomogeneousPoly n :=
  ⟨MvPolynomial.monomial m c, MvPolynomial.isHomogeneous_monomial c (by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]
    exact h)⟩

theorem X_mul_pderiv0_monomial (j : Fin 3) (s : Fin 3 →₀ ℕ) (c : ℂ) :
    (X j : Poly) * pderiv 0 (monomial s c) =
      monomial (Finsupp.single j 1 + (s - Finsupp.single 0 1)) (c * (s 0 : ℂ)) := by
  rw [MvPolynomial.pderiv_monomial]
  change monomial (Finsupp.single j 1) (1 : ℂ) * _ = _
  rw [MvPolynomial.monomial_mul_monomial, one_mul]

theorem radInf0_monoHP (hn : 0 < n) (s : Fin 3 →₀ ℕ) (c : ℂ) (h : s 0 + s 1 + s 2 = n) :
    (radicalInfinitesimal n hn 0 (monoHP n s c h)).val =
      monomial (Finsupp.single 1 1 + (s - Finsupp.single 0 1)) (c * (s 0 : ℂ)) :=
  X_mul_pderiv0_monomial 1 s c

theorem radInf1_monoHP (hn : 0 < n) (s : Fin 3 →₀ ℕ) (c : ℂ) (h : s 0 + s 1 + s 2 = n) :
    (radicalInfinitesimal n hn 1 (monoHP n s c h)).val =
      monomial (Finsupp.single 2 1 + (s - Finsupp.single 0 1)) (c * (s 0 : ℂ)) :=
  X_mul_pderiv0_monomial 2 s c

theorem aux_exps (m : Fin 3 →₀ ℕ) (j : Fin 3) (hj : j = 1 ∨ j = 2) (hm : 1 ≤ m j) :
    Finsupp.single j 1 + (m + Finsupp.single 0 1 - Finsupp.single j 1 - Finsupp.single 0 1) =
      m := by
  ext k
  rcases hj with rfl | rfl <;> fin_cases k <;>
    simp [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega

/-- **The kernel of `κ` is `N₀V + N₁V`.** -/
theorem mem_Wsp_of_kappaB (hn : 0 < n) (v : HomogeneousPoly n) (hv : kappaB n v = 0) :
    v ∈ LinearMap.range (radicalInfinitesimal n hn 0) ⊔
      LinearMap.range (radicalInfinitesimal n hn 1) := by
  let Wp : Submodule ℂ Poly := (LinearMap.range (radicalInfinitesimal n hn 0) ⊔
    LinearMap.range (radicalInfinitesimal n hn 1)).map (HomogeneousPoly n).subtype
  suffices h : v.val ∈ Wp by
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp h
    rwa [show w = v from Subtype.ext hwv] at hw
  rw [v.val.as_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  have hc : v.val.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hdeg := deg3 n v hc
  have hne : ¬ (m 1 = 0 ∧ m 2 = 0) := by
    rintro ⟨h1, h2⟩
    apply hc
    have : m = Finsupp.single 0 n := by
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Finsupp.single_eq_same]
        omega
      · simp [h1]
      · simp [h2]
    rw [this]
    exact hv
  by_cases h1 : m 1 = 0
  · have h2 : m 2 ≠ 0 := fun h2 => hne ⟨h1, h2⟩
    have hs := aux_exps m 2 (Or.inr rfl) (Nat.one_le_iff_ne_zero.mpr h2)
    have e0 : ((m + Finsupp.single 0 1 - Finsupp.single 2 1 : Fin 3 →₀ ℕ) 0) = m 0 + 1 := by
      simp
    have e1 : ((m + Finsupp.single 0 1 - Finsupp.single 2 1 : Fin 3 →₀ ℕ) 1) = m 1 := by
      simp
    have e2 : ((m + Finsupp.single 0 1 - Finsupp.single 2 1 : Fin 3 →₀ ℕ) 2) = m 2 - 1 := by
      simp
    have hsum : ((m + Finsupp.single 0 1 - Finsupp.single 2 1 : Fin 3 →₀ ℕ) 0) +
        ((m + Finsupp.single 0 1 - Finsupp.single 2 1 : Fin 3 →₀ ℕ) 1) +
        ((m + Finsupp.single 0 1 - Finsupp.single 2 1 : Fin 3 →₀ ℕ) 2) = n := by
      rw [e0, e1, e2]
      omega
    have key : (radicalInfinitesimal n hn 1 (monoHP n (m + Finsupp.single 0 1 - Finsupp.single 2 1)
        (v.val.coeff m / ((m 0 : ℂ) + 1)) hsum)).val =
        monomial m (v.val.coeff m) := by
      rw [radInf1_monoHP, hs, e0]
      congr 1
      have : ((m 0 : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m 0)
      push_cast
      field_simp
    exact Submodule.mem_map.mpr ⟨_, Submodule.mem_sup_right (LinearMap.mem_range_self _ _), key⟩
  · have hs := aux_exps m 1 (Or.inl rfl) (Nat.one_le_iff_ne_zero.mpr h1)
    have e0 : ((m + Finsupp.single 0 1 - Finsupp.single 1 1 : Fin 3 →₀ ℕ) 0) = m 0 + 1 := by
      simp
    have e1 : ((m + Finsupp.single 0 1 - Finsupp.single 1 1 : Fin 3 →₀ ℕ) 1) = m 1 - 1 := by
      simp
    have e2 : ((m + Finsupp.single 0 1 - Finsupp.single 1 1 : Fin 3 →₀ ℕ) 2) = m 2 := by
      simp
    have hsum : ((m + Finsupp.single 0 1 - Finsupp.single 1 1 : Fin 3 →₀ ℕ) 0) +
        ((m + Finsupp.single 0 1 - Finsupp.single 1 1 : Fin 3 →₀ ℕ) 1) +
        ((m + Finsupp.single 0 1 - Finsupp.single 1 1 : Fin 3 →₀ ℕ) 2) = n := by
      rw [e0, e1, e2]
      omega
    have key : (radicalInfinitesimal n hn 0 (monoHP n (m + Finsupp.single 0 1 - Finsupp.single 1 1)
        (v.val.coeff m / ((m 0 : ℂ) + 1)) hsum)).val =
        monomial m (v.val.coeff m) := by
      rw [radInf0_monoHP, hs, e0]
      congr 1
      have : ((m 0 : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m 0)
      push_cast
      field_simp
    exact Submodule.mem_map.mpr ⟨_, Submodule.mem_sup_left (LinearMap.mem_range_self _ _), key⟩

/-! ### The coboundary criterion -/

theorem radicalDifference_range (hn : 0 < n) (i : Fin 2) (γ : HomogeneousPoly n) :
    ∃ δ, radicalDifference n i δ = radicalInfinitesimal n hn i γ := by
  let E : HomogeneousPoly n ≃ₗ[ℂ] HomogeneousPoly n :=
    finiteExponentialRatioEquiv n (-(radicalInfinitesimal n hn i))
      (radicalInfinitesimal_nilpotent n hn i).neg
  have hNrm : radicalDifferenceNormalization n hn i = E.symm := rfl
  have hEapp : ∀ y, E y = finiteExponentialRatio n (-(radicalInfinitesimal n hn i)) y :=
    fun y => rfl
  have hc : ∀ y, finiteExponentialRatio n (-(radicalInfinitesimal n hn i))
      (radicalInfinitesimal n hn i y) =
      radicalInfinitesimal n hn i (finiteExponentialRatio n (-(radicalInfinitesimal n hn i)) y) := by
    intro y
    have h := (finiteExponentialRatio_commute n (-(radicalInfinitesimal n hn i))
      (radicalInfinitesimal n hn i) (Commute.refl (radicalInfinitesimal n hn i)).neg_left).eq
    exact LinearMap.congr_fun h y
  have hEc : ∀ y, E (radicalInfinitesimal n hn i y) = radicalInfinitesimal n hn i (E y) := by
    intro y
    rw [hEapp, hEapp]
    exact hc y
  have hcomm : ∀ x, E.symm (radicalInfinitesimal n hn i x) =
      radicalInfinitesimal n hn i (E.symm x) := by
    intro x
    apply E.injective
    rw [LinearEquiv.apply_symm_apply, hEc, LinearEquiv.apply_symm_apply]
  refine ⟨-(E.symm γ), ?_⟩
  apply E.symm.injective
  rw [← hNrm, radicalDifferenceNormalization_difference, hNrm, hcomm, map_neg, neg_neg]

/-- **A two-cocycle on the upper line radical is a coboundary when `κ` kills its alternation.** -/
theorem radical_H2_zero (hn : 0 < n)
    (G : groupCohomology.cocycles₂ (Rep.of (radicalRepresentation n)))
    (hG : kappaB n (latticeTwoCocycleAlternation (Rep.of (radicalRepresentation n)) G) = 0) :
    groupCohomology.H2π (Rep.of (radicalRepresentation n)) G = 0 := by
  obtain ⟨y, ⟨γ₀, rfl⟩, w, ⟨γ₁, rfl⟩, hyw⟩ := Submodule.mem_sup.mp (mem_Wsp_of_kappaB n hn _ hG)
  apply (latticeTwoCocycle_H2_zero_iff _ G).mpr
  obtain ⟨β, hβ⟩ := radicalDifference_range n hn 0 γ₀
  obtain ⟨α, hα⟩ := radicalDifference_range n hn 1 (-γ₁)
  refine ⟨α, β, ?_⟩
  have e0 : ((Rep.of (radicalRepresentation n)).ρ radicalLatticeFirst - 1) β =
      radicalDifference n 0 β := by
    change (radicalRepresentation n radicalLatticeFirst - 1) β = _
    have h : radicalRepresentation n radicalLatticeFirst =
        rationalCoefficientComponent n trivialCharacter (radicalGenerator 0) :=
      radicalRepresentation_generator n 0
    rw [h]
    rfl
  have e1 : ((Rep.of (radicalRepresentation n)).ρ radicalLatticeSecond - 1) α =
      radicalDifference n 1 α := by
    change (radicalRepresentation n radicalLatticeSecond - 1) α = _
    have h : radicalRepresentation n radicalLatticeSecond =
        rationalCoefficientComponent n trivialCharacter (radicalGenerator 1) :=
      radicalRepresentation_generator n 1
    rw [h]
    rfl
  rw [e0, e1, hβ, hα, ← hyw, map_neg, sub_neg_eq_add]

/-- The restriction of a two-cocycle of `ΛB` to the radical. -/
def radG (c : groupCohomology.cocycles₂ (Aρ (ρn n))) :
    groupCohomology.cocycles₂ (Rep.of (radicalRepresentation n)) :=
  ⟨fun ab => c (ψ (SemidirectProduct.inl ab.1), ψ (SemidirectProduct.inl ab.2)), (groupCohomology.mem_cocycles₂_iff _).mpr (by
    intro a b d
    have key := (groupCohomology.mem_cocycles₂_iff _).mp c.property
      (ψ (SemidirectProduct.inl a)) (ψ (SemidirectProduct.inl b)) (ψ (SemidirectProduct.inl d))
    have hrep : ∀ (x : Multiplicative (ℤ × ℤ)) (v : HomogeneousPoly n),
        radicalRepresentation n x v =
          ρn n ((ψ (SemidirectProduct.inl x) : ΛB) : RationalGL3) v := by
      intro x v
      have := congrArg (fun r => r x v) (standardBadLineRepresentation_radical n)
      exact this.symm
    let cv : ΛB → ΛB → HomogeneousPoly n := fun x y => c (x, y)
    change cv (ψ (SemidirectProduct.inl (a * b))) (ψ (SemidirectProduct.inl d)) +
        cv (ψ (SemidirectProduct.inl a)) (ψ (SemidirectProduct.inl b)) =
      radicalRepresentation n a (cv (ψ (SemidirectProduct.inl b)) (ψ (SemidirectProduct.inl d))) +
        cv (ψ (SemidirectProduct.inl a)) (ψ (SemidirectProduct.inl (b * d)))
    rw [hrep]
    simp only [map_mul]
    exact key)⟩

/-- **The radical restriction of the class of `c` vanishes when `κ` kills the alternation of
`c|_U`.** -/
theorem radicalRestriction_zero (hn : 0 < n) (c : groupCohomology.cocycles₂ (Aρ (ρn n)))
    (hc : kappaB n (c (Ux (1, 0), Ux (0, 1)) - c (Ux (0, 1), Ux (1, 0))) = 0) :
    radicalRestrictionH2 integralBadLineSplitting.conjAct (standardBadLineRepresentation n)
        ((inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ (modelCycle n c)) = 0 := by
  have h0 : groupCohomology.H2π (Rep.of (radicalRepresentation n)) (radG n c) = 0 :=
    radical_H2_zero n hn (radG n c) hc
  rw [groupCohomology.H2π_eq_zero_iff] at h0
  obtain ⟨f, hf⟩ := h0
  change Multiplicative (ℤ × ℤ) → HomogeneousPoly n at f
  have eq : ∀ a b : Multiplicative (ℤ × ℤ),
      radicalRepresentation n a (f b) - f (a * b) + f a =
        c (ψ (SemidirectProduct.inl a), ψ (SemidirectProduct.inl b)) :=
    fun a b => congrFun hf (a, b)
  change inhomogeneousPullbackH2 SemidirectProduct.inl (standardBadLineRepresentation n)
    ((inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ (modelCycle n c)) = 0
  rw [inhomogeneousPullbackH2_mk]
  refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨f, ?_⟩
  apply Subtype.ext
  funext a b
  have hrep : ((standardBadLineRepresentation n).comp SemidirectProduct.inl) a (f b) =
      radicalRepresentation n a (f b) := by
    rw [standardBadLineRepresentation_radical]
  change ((standardBadLineRepresentation n).comp SemidirectProduct.inl) a (f b) - f (a * b) + f a =
    c (ψ (SemidirectProduct.inl a), ψ (SemidirectProduct.inl b))
  rw [hrep]
  exact eq a b

end TernaryPeriodPolynomials.LevelThree.BadLineKernel
