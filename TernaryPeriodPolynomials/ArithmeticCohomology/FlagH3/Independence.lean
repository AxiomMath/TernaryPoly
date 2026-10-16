module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Data

@[expose] public section



/-!
# Independence of the flag functional from the choice of Heisenberg coordinates

Formalized by Claude Sonnet 5.5.

* `cocycleClass_eq_of_dTwo`: cocycles differing by `dα` have the same class in `H³(B, ℚ)`.
* `theta_change`: if `a' = α a`, `b' = β b`, `c' = αβ c + s a + t b` with `α² = β² = 1` (a change of Heisenberg coordinates by an upper triangular matrix of determinant `1`), the cocycles `θ'`, `θ` differ by the coboundary
  `dγ`, `γ(x₀,x₁) = 2αβ (s b(x₀) a(x₁)² / 2 + t b(x₀) c(x₁))`.
* `unit_coords`: the corresponding algebra for the entries of `M' β = β M`.
* `flagData_lam_eq`: the evaluation functionals of two flag data with such related coordinates (and equal `p²q²`) coincide.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FlagH3

open CategoryTheory

variable {B : Type} [Group B]

set_option backward.isDefEq.respectTransparency false in
/-- Cohomologous cocycles have the same class: if `θ' = θ + dα`, the classes agree. -/
theorem cocycleClass_eq_of_dTwo (θ θ' : (Fin 3 → B) → ℚ) (hθ : dThree θ = 0) (hθ' : dThree θ' = 0)
    (α : (Fin 2 → B) → ℚ) (h : θ' = θ + dTwo α) : cocycleClass θ' hθ' = cocycleClass θ hθ := by
  have hmono : Function.Injective (groupCohomology.iCocycles (Rep.trivial ℚ B ℚ) 3).hom := by
    have := (ModuleCat.mono_iff_injective (groupCohomology.iCocycles (Rep.trivial ℚ B ℚ) 3)).1 inferInstance
    exact this
  have hd : (groupCohomology.iCocycles (Rep.trivial ℚ B ℚ) 3).hom
      ((groupCohomology.toCocycles (Rep.trivial ℚ B ℚ) 2 3).hom α) = dTwo α := by
    have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      ((groupCohomology.inhomogeneousCochains (Rep.trivial ℚ B ℚ)).toCycles_i 2 3)) α
    exact this
  have hsum : groupCohomology.cocyclesMk θ' hθ' = groupCohomology.cocyclesMk θ hθ +
      (groupCohomology.toCocycles (Rep.trivial ℚ B ℚ) 2 3).hom α := by
    apply hmono
    rw [map_add, hd]
    have e1 := groupCohomology.iCocycles_mk (A := Rep.trivial ℚ B ℚ) θ' hθ'
    have e2 := groupCohomology.iCocycles_mk (A := Rep.trivial ℚ B ℚ) θ hθ
    exact e1.trans (h.trans (congrArg (fun t => t + dTwo α) e2.symm))
  unfold cocycleClass
  rw [hsum, map_add]
  have h0 : (groupCohomology.π (Rep.trivial ℚ B ℚ) 3).hom
      ((groupCohomology.toCocycles (Rep.trivial ℚ B ℚ) 2 3).hom α) = 0 := by
    have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      ((groupCohomology.inhomogeneousCochains (Rep.trivial ℚ B ℚ)).toCycles_comp_homologyπ 2 3)) α
    exact this
  rw [h0, add_zero]


namespace HeisCoords

/-- **Change of Heisenberg coordinates** (conjugation by an upper triangular matrix of determinant `1`): if `a' = α a`, `b' = β b`, `c' = αβ c + s a + t b` with `α² = β² = 1`, then the cocycles
`θ`, `θ'` are cohomologous, with an explicit primitive. -/
theorem theta_change (H H' : HeisCoords B) (α β s t : ℤ) (hα : α * α = 1) (hβ : β * β = 1)
    (ha : ∀ p, H'.a p = α * H.a p) (hb : ∀ p, H'.b p = β * H.b p)
    (hc : ∀ p, H'.c p = α * β * H.c p + s * H.a p + t * H.b p) :
    cocycleClass H'.theta H'.theta_cocycle = cocycleClass H.theta H.theta_cocycle := by
  refine cocycleClass_eq_of_dTwo _ _ _ _
    (fun x => (2 * (α : ℚ) * β) * ((s : ℚ) * H.b (x 0) * (H.a (x 1)) ^ 2 / 2 + (t : ℚ) * H.b (x 0) * H.c (x 1))) ?_
  funext g
  have hα' : (α : ℚ) * α = 1 := by exact_mod_cast hα
  have hβ' : (β : ℚ) * β = 1 := by exact_mod_cast hβ
  simp [theta, dTwo_apply, ha, hb, hc, H.a_mul, H.b_mul, H.c_mul]
  linear_combination ((H.b (g 0) : ℚ) * H.a (g 1) * (2 * H.c (g 2) + H.a (g 1) * H.b (g 2)) * ((β : ℚ) * β)) * hα' +
    ((H.b (g 0) : ℚ) * H.a (g 1) * (2 * H.c (g 2) + H.a (g 1) * H.b (g 2))) * hβ'

end HeisCoords


theorem unit_sq {e1 e2 e3 : ℤ} (pr : e1 * e2 * e3 = 1) : e1 * e1 = 1 ∧ e2 * e2 = 1 ∧ e3 * e3 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rcases Int.eq_one_or_neg_one_of_mul_eq_one (show e1 * (e2 * e3) = 1 by linarith) with h | h <;> simp [h]
  · rcases Int.eq_one_or_neg_one_of_mul_eq_one (show e2 * (e1 * e3) = 1 by linarith) with h | h <;> simp [h]
  · rcases Int.eq_one_or_neg_one_of_mul_eq_one (show e3 * (e1 * e2) = 1 by linarith) with h | h <;> simp [h]

/-- Pure algebra of the change of coordinates under an upper triangular matrix of determinant `1`: the coordinates
change by `α = e₁e₂`, `β = e₂e₃`, `s = -z`, `t = e₃ x`. -/
theorem unit_coords {e1 e2 e3 x z a b c a' b' c' : ℤ} (pr : e1 * e2 * e3 = 1) (Ea : a' * e2 = e1 * a)
    (Eb : b' * e3 = e2 * b) (Ec : c' * e3 = e1 * c + x * b - a' * z) :
    a' = (e1 * e2) * a ∧ b' = (e2 * e3) * b ∧ c' = (e1 * e2) * (e2 * e3) * c + (-z) * a + (e3 * x) * b := by
  obtain ⟨u1, u2, u3⟩ := unit_sq pr
  have ha : a' = (e1 * e2) * a := by linear_combination e2 * Ea - a' * u2
  have hb : b' = (e2 * e3) * b := by linear_combination e3 * Eb - b' * u3
  exact ⟨ha, hb, by linear_combination e3 * Ec - c' * u3 - e1 * e3 * c * u2 - z * a * pr - e3 * z * ha⟩

namespace FlagCohomDatum

theorem lam_eq_of_z (D D' : FlagCohomDatum B) (h : D.z = D'.z) : D.lam = D'.lam := by
  cases D
  cases D'
  simp only at h
  subst h
  rfl

/-- Two functionals on a one-dimensional space which agree on a vector where they do not vanish are equal. -/
theorem lam_eq_of (D D' : FlagCohomDatum B) (w : groupCohomology (Rep.trivial ℚ B ℚ) 3) (hw : D.lam w ≠ 0)
    (h : D'.lam w = D.lam w) : D.lam = D'.lam := by
  have := D.finite
  have hw0 : w ≠ 0 := fun h0 => hw (by rw [h0, map_zero])
  have hv := (finrank_eq_one_iff_of_nonzero' w hw0).mp D.finrank_eq_one
  ext x
  obtain ⟨c, rfl⟩ := hv x
  simp [h]

end FlagCohomDatum

namespace HeisCoords

variable (H : HeisCoords B)

/-- The value of the functional of `flagData` on the Heisenberg class `[θ]`. -/
theorem flagData_lam_theta (E : GroupExtension (Multiplicative (ℤ × ℤ)) B (Multiplicative ℤ)) (X Y : B) (p q : ℤ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hXa : H.a X = p) (hXb : H.b X = 0) (hXc : H.c X = 0) (hYa : H.a Y = 0)
    (hYb : H.b Y = q) (hYc : H.c Y = 0) :
    (H.flagData E X Y p q hp hq hXa hXb hXc hYa hYb hYc).lam (cocycleClass H.theta H.theta_cocycle) =
      -2 * (p : ℚ) ^ 2 * (q : ℚ) ^ 2 :=
  (FlagCohomDatum.lam_cocycle _ _ _).trans (H.cycle_theta X Y p q hXa hXb hXc hYa hYb hYc)

/-- **The functionals of two flag data with cohomologous Heisenberg cocycles agree** (when `p²q²` agree). -/
theorem flagData_lam_eq (H H' : HeisCoords B) (α β s t : ℤ) (hα : α * α = 1) (hβ : β * β = 1)
    (ha : ∀ p, H'.a p = α * H.a p) (hb : ∀ p, H'.b p = β * H.b p)
    (hc : ∀ p, H'.c p = α * β * H.c p + s * H.a p + t * H.b p)
    (E E' : GroupExtension (Multiplicative (ℤ × ℤ)) B (Multiplicative ℤ)) (X Y X' Y' : B) (p q p' q' : ℤ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hp' : p' ≠ 0) (hq' : q' ≠ 0)
    (hXa : H.a X = p) (hXb : H.b X = 0) (hXc : H.c X = 0) (hYa : H.a Y = 0) (hYb : H.b Y = q) (hYc : H.c Y = 0)
    (hXa' : H'.a X' = p') (hXb' : H'.b X' = 0) (hXc' : H'.c X' = 0) (hYa' : H'.a Y' = 0) (hYb' : H'.b Y' = q')
    (hYc' : H'.c Y' = 0) (hpq : (p : ℚ) ^ 2 * (q : ℚ) ^ 2 = (p' : ℚ) ^ 2 * (q' : ℚ) ^ 2) :
    (H.flagData E X Y p q hp hq hXa hXb hXc hYa hYb hYc).lam =
      (H'.flagData E' X' Y' p' q' hp' hq' hXa' hXb' hXc' hYa' hYb' hYc').lam := by
  have h1 := H.flagData_lam_theta E X Y p q hp hq hXa hXb hXc hYa hYb hYc
  have h2 := H'.flagData_lam_theta E' X' Y' p' q' hp' hq' hXa' hXb' hXc' hYa' hYb' hYc'
  rw [theta_change H H' α β s t hα hβ ha hb hc] at h2
  refine FlagCohomDatum.lam_eq_of _ _ _ ?_ (h2.trans (h1.symm ▸ (by linear_combination 2 * hpq)))
  rw [h1]
  have hp'' : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hq'' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  positivity

end HeisCoords

end TernaryPeriodPolynomials.Argument.FlagH3
