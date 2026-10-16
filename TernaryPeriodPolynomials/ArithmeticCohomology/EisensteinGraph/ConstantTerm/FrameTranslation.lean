module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.FrameSemidirect
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.CoefficientFiltration

@[expose] public section


/-!
# Conjugation by a rational radical point acts on the level lattice by a twist

Let `F` be a radical frame, `N` a level and `v ∈ ℚ²` with `v - A_m v ∈ ℤ²` for every Levi element
`m` of level `N`. Conjugation by the rational radical point `h = u(v)` preserves
`F.latticeHom N` and corresponds, on the semidirect product `Lat ⋊ leviLevel N`, to the
endomorphism `twistHom` `⟨ℓ, m⟩ ↦ ⟨ℓ · δ(m), m⟩` with `δ(m) = v - A_m v`.

Written by AxiomCode.
-/

open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

section Twist

variable {L M : Type} [CommGroup L] [Group M] (action : M →* MulAut L)

/-- The endomorphism `⟨ℓ, m⟩ ↦ ⟨ℓ δ(m), m⟩` of `L ⋊ M` attached to a crossed homomorphism `δ`. -/
def twistHom (δ : M → L) (hδ : ∀ m m', δ (m * m') = δ m * action m (δ m')) :
    SemidirectProduct L M action →* SemidirectProduct L M action where
  toFun g := ⟨g.left * δ g.right, g.right⟩
  map_one' := by
    have h1 : δ 1 = 1 := by
      have h := hδ 1 1
      rw [mul_one, map_one, MulAut.one_apply] at h
      exact mul_left_cancel (a := δ 1) (by rw [mul_one]; exact h.symm)
    apply SemidirectProduct.ext
    · change (1 : SemidirectProduct L M action).left * δ (1 : SemidirectProduct L M action).right = _
      simp [h1]
    · rfl
  map_mul' g g' := by
    apply SemidirectProduct.ext
    · change (g * g').left * δ (g * g').right =
        (g.left * δ g.right) * action g.right (g'.left * δ g'.right)
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, hδ, map_mul]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    · rfl

theorem twistHom_inl (δ : M → L) (hδ : ∀ m m', δ (m * m') = δ m * action m (δ m'))
    (ℓ : L) : twistHom action δ hδ (SemidirectProduct.inl ℓ) = SemidirectProduct.inl ℓ := by
  have h1 : δ 1 = 1 := by
    have h := hδ 1 1
    rw [mul_one, map_one, MulAut.one_apply] at h
    exact mul_left_cancel (a := δ 1) (by rw [mul_one]; exact h.symm)
  apply SemidirectProduct.ext
  · change ℓ * δ 1 = ℓ
    rw [h1, mul_one]
  · rfl

theorem twistHom_right (δ : M → L) (hδ : ∀ m m', δ (m * m') = δ m * action m (δ m'))
    (g : SemidirectProduct L M action) : (twistHom action δ hδ g).right = g.right := rfl

theorem twistHom_left (δ : M → L) (hδ : ∀ m m', δ (m * m') = δ m * action m (δ m'))
    (g : SemidirectProduct L M action) :
    (twistHom action δ hδ g).left = g.left * δ g.right := rfl

end Twist

theorem leviAct_add (A : GLTwo ℤ) (r s : ℚ × ℚ) :
    leviAct A (r + s) = leviAct A r + leviAct A s := by
  simp only [leviAct, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  ext <;> simp <;> ring

theorem leviAct_neg (A : GLTwo ℤ) (r : ℚ × ℚ) : leviAct A (-r) = -leviAct A r := by
  simp only [leviAct, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
  ext <;> simp <;> ring

theorem leviAct_mul (A B : GLTwo ℤ) (r : ℚ × ℚ) :
    leviAct (A * B) r = leviAct A (leviAct B r) := by
  simp only [leviAct, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ext <;> simp <;> ring

theorem leviAct_sub (A : GLTwo ℤ) (r s : ℚ × ℚ) :
    leviAct A (r - s) = leviAct A r - leviAct A s := by
  rw [sub_eq_add_neg, leviAct_add, leviAct_neg, ← sub_eq_add_neg]

namespace RadicalFrame

variable (F : RadicalFrame)

/-- The radical point with rational coordinates `r`. -/
def point (r : ℚ × ℚ) : RationalGL3 := F.radical (Multiplicative.ofAdd r)

theorem point_add (r s : ℚ × ℚ) : F.point (r + s) = F.point r * F.point s := by
  rw [point, point, point, ofAdd_add, map_mul]

theorem point_zero : F.point 0 = 1 := by
  rw [point, ofAdd_zero, map_one]

theorem point_neg (r : ℚ × ℚ) : F.point (-r) = (F.point r)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← point_add, neg_add_cancel, point_zero]

theorem point_comm (r s : ℚ × ℚ) : F.point r * F.point s = F.point s * F.point r := by
  rw [← point_add, ← point_add, add_comm]

theorem integral_eq_point (ℓ : ℤ × ℤ) : F.integral ℓ = F.point ((ℓ.1 : ℚ), (ℓ.2 : ℚ)) := rfl

theorem levi_mul_point (m : F.Levi) (r : ℚ × ℚ) :
    F.leviHom m * F.point r = F.point (leviAct (F.leviMatrix m) r) * F.leviHom m := by
  have h := F.conj m r
  change F.leviHom m * F.point r * (F.leviHom m)⁻¹ = F.point (leviAct (F.leviMatrix m) r) at h
  rw [← h]
  group

/-- Conjugation of a Levi element by the radical point `u(v)`. -/
theorem point_conj_levi (m : F.Levi) (v : ℚ × ℚ) :
    F.point v * F.leviHom m * (F.point v)⁻¹ =
      F.point (v - leviAct (F.leviMatrix m) v) * F.leviHom m := by
  rw [← point_neg, mul_assoc, levi_mul_point, leviAct_neg, ← mul_assoc, ← point_add,
    ← sub_eq_add_neg]

theorem point_pow (r : ℚ × ℚ) (k : ℕ) : F.point (k • r) = (F.point r) ^ k := by
  induction k with
  | zero => rw [zero_smul, point_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, point_add, ih, pow_succ]

section Shift

variable (N : ℕ) (v : ℚ × ℚ)
  (hv : ∀ m : F.leviLevel N, ∃ δ : ℤ × ℤ,
    ((δ.1 : ℚ), (δ.2 : ℚ)) = v - leviAct (F.leviMatrix (m : F.Levi)) v)

/-- The integral crossed homomorphism `m ↦ v - A_m v`. -/
def shiftCocycle (m : F.leviLevel N) : Lat :=
  Multiplicative.ofAdd (Classical.choose (hv m))

theorem shiftCocycle_spec (m : F.leviLevel N) :
    (((Multiplicative.toAdd (F.shiftCocycle N v hv m)).1 : ℚ),
      ((Multiplicative.toAdd (F.shiftCocycle N v hv m)).2 : ℚ)) =
      v - leviAct (F.leviMatrix (m : F.Levi)) v :=
  Classical.choose_spec (hv m)

theorem shiftCocycle_mul (m m' : F.leviLevel N) :
    F.shiftCocycle N v hv (m * m') =
      F.shiftCocycle N v hv m * (F.latticeAction N m) (F.shiftCocycle N v hv m') := by
  have e1 := F.shiftCocycle_spec N v hv (m * m')
  have e2 := F.shiftCocycle_spec N v hv m
  have e3 := F.shiftCocycle_spec N v hv m'
  have e4 : (((Multiplicative.toAdd ((F.latticeAction N m) (F.shiftCocycle N v hv m'))).1 : ℚ),
      ((Multiplicative.toAdd ((F.latticeAction N m) (F.shiftCocycle N v hv m'))).2 : ℚ)) =
        leviAct (F.leviMatrix (m : F.Levi)) (v - leviAct (F.leviMatrix (m' : F.Levi)) v) := by
    rw [← e3]
    exact (leviAct_intCast (F.leviMatrix (m : F.Levi))
      (Multiplicative.toAdd (F.shiftCocycle N v hv m'))).symm
  apply Multiplicative.toAdd.injective
  apply Prod.ext
  · apply Int.cast_injective (α := ℚ)
    have h1 := congrArg Prod.fst e1
    have h2 := congrArg Prod.fst e2
    have h4 := congrArg Prod.fst e4
    simp only [Subgroup.coe_mul, map_mul, leviAct_mul, leviAct_sub, Prod.fst_sub] at h1 h2 h4
    simp only [toAdd_mul, Prod.fst_add, Int.cast_add]
    linear_combination h1 - h2 - h4
  · apply Int.cast_injective (α := ℚ)
    have h1 := congrArg Prod.snd e1
    have h2 := congrArg Prod.snd e2
    have h4 := congrArg Prod.snd e4
    simp only [Subgroup.coe_mul, map_mul, leviAct_mul, leviAct_sub, Prod.snd_sub] at h1 h2 h4
    simp only [toAdd_mul, Prod.snd_add, Int.cast_add]
    linear_combination h1 - h2 - h4

/-- The twist of `Lat ⋊ leviLevel N` induced by conjugation with the radical point `u(v)`. -/
def shiftHom : SemidirectProduct Lat (F.leviLevel N) (F.latticeAction N) →*
    SemidirectProduct Lat (F.leviLevel N) (F.latticeAction N) :=
  twistHom (F.latticeAction N) (F.shiftCocycle N v hv) (F.shiftCocycle_mul N v hv)

theorem latticeHom_shiftHom (g : SemidirectProduct Lat (F.leviLevel N) (F.latticeAction N)) :
    F.latticeHom N (F.shiftHom N v hv g) =
      F.point v * F.latticeHom N g * (F.point v)⁻¹ := by
  rw [latticeHom_apply, latticeHom_apply]
  change F.integral (Multiplicative.toAdd (g.left * F.shiftCocycle N v hv g.right)) *
      F.leviHom (g.right : F.Levi) = _
  have hδ : F.integral (Multiplicative.toAdd (F.shiftCocycle N v hv g.right)) =
      F.point (v - leviAct (F.leviMatrix (g.right : F.Levi)) v) := by
    rw [integral_eq_point, F.shiftCocycle_spec N v hv g.right]
  rw [toAdd_mul, F.integral_add, hδ, mul_assoc, ← point_conj_levi, integral_eq_point]
  have hc : F.point v * F.point ((((Multiplicative.toAdd g.left).1 : ℚ),
      ((Multiplicative.toAdd g.left).2 : ℚ))) =
      F.point ((((Multiplicative.toAdd g.left).1 : ℚ),
        ((Multiplicative.toAdd g.left).2 : ℚ))) * F.point v := point_comm _ _ _
  calc F.point (((Multiplicative.toAdd g.left).1 : ℚ), ((Multiplicative.toAdd g.left).2 : ℚ)) *
        (F.point v * F.leviHom (g.right : F.Levi) * (F.point v)⁻¹)
      = (F.point v * F.point (((Multiplicative.toAdd g.left).1 : ℚ),
          ((Multiplicative.toAdd g.left).2 : ℚ))) * F.leviHom (g.right : F.Levi) *
            (F.point v)⁻¹ := by rw [hc]; group
    _ = _ := by group

end Shift

/-- Unipotent radical points act nilpotently on the coefficients: if `h ∈ conjUnitri q` then
`(ρ h - 1)^(2n+1) = 0`. -/
theorem nilpotent_of_conjUnitri {n : ℕ} (χ : RankOneCharacter) {q h : RationalGL3}
    (hh : h ∈ TernaryPeriodPolynomials.FlagExactness.conjUnitri q) :
    (rationalCoefficientComponent n χ h - 1) ^ (2 * n + 1) = 0 := by
  have key : ∀ i : ℕ,
      ∀ w ∈ TernaryPeriodPolynomials.FlagExactness.Weight.flagFiltration n χ q i,
      ((rationalCoefficientComponent n χ h - 1) ^ i) w = 0 := by
    intro i
    induction i with
    | zero =>
      intro w hw
      rw [TernaryPeriodPolynomials.FlagExactness.Weight.flagFiltration_zero] at hw
      rw [(Submodule.mem_bot ℂ).mp hw]
      simp
    | succ i ih =>
      intro w hw
      have hstep := TernaryPeriodPolynomials.FlagExactness.Weight.flagFiltration_step
        χ hh i w hw
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (by simpa using hstep)
  apply LinearMap.ext
  intro w
  rw [LinearMap.zero_apply]
  exact key (2 * n + 1) w
    (TernaryPeriodPolynomials.FlagExactness.Weight.flagFiltration_top n χ q w)

end RadicalFrame

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
