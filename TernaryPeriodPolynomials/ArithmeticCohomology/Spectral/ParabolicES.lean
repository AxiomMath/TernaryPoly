module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneHeckeH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.PeterssonSemisimple

@[expose] public section


/-!
# Parabolic Eichler–Shimura at level one, and multiplicity one in `H¹(GL₂(ℤ), Sym^d ⊗ det^σ)`

Let `β` be a nonzero linear functional on `H¹(SL₂(ℤ), Sym^d)` (`d = 2r ≥ 2`) killing the restrictions
of the period classes of both twists. Since `dim H¹(SL₂(ℤ), Sym^d) = 2 dim S_{d+2} + 1`, the two
twists restrict injectively and independently, and each period map is injective, a dimension count
shows that for both twists `σ` the classes `x` with `β(res x) = 0` are exactly the period classes:
`ker (β ∘ res_σ) = range per_σ` (`ker_eq_range_period`).

If moreover `β ∘ res_σ` is an eigenfunctional of the Hecke operator `T_{p₀}` with eigenvalue `q` and
the eigenvalue `e_{p₀} ≠ q`, then every joint generalized eigenclass of the `T_p` (`p ≠ 3`) with
eigenvalues `e_p` is a period class, of a joint generalized eigenform with eigenvalues `p^σ e_p`.
Generalized multiplicity one for level-one cusp forms (Petersson semisimplicity plus strong
multiplicity one away from `3`) then bounds the joint generalized eigenspace in `H¹` by one
(`finrank_jointGenEigenspace_H1_le_one`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups
open GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.ParabolicES

section Generic

variable {C X₀ X₁ Y : Type*} [AddCommGroup C] [Module ℂ C] [AddCommGroup X₀] [Module ℂ X₀]
  [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup Y] [Module ℂ Y]

/-- **Dimension count.** Two injective "period maps" from `C` into two spaces which jointly embed
into `Y`, with `dim Y = 2 dim C + 1`, fill the kernels of a nonzero functional vanishing on them. -/
theorem ker_eq_range_of_finrank [FiniteDimensional ℂ C] [FiniteDimensional ℂ X₀]
    [FiniteDimensional ℂ X₁] [FiniteDimensional ℂ Y]
    (r₀ : X₀ →ₗ[ℂ] Y) (r₁ : X₁ →ₗ[ℂ] Y) (hinj : Function.Injective (r₀.coprod r₁))
    (β : Y →ₗ[ℂ] ℂ) (hβ : β ≠ 0) (per₀ : C →ₗ[ℂ] X₀) (per₁ : C →ₗ[ℂ] X₁)
    (inj₀ : Function.Injective per₀) (inj₁ : Function.Injective per₁)
    (hY : Module.finrank ℂ Y = 2 * Module.finrank ℂ C + 1)
    (hv₀ : ∀ f, β (r₀ (per₀ f)) = 0) (hv₁ : ∀ f, β (r₁ (per₁ f)) = 0) :
    LinearMap.ker (β ∘ₗ r₀) = LinearMap.range per₀ ∧
      LinearMap.ker (β ∘ₗ r₁) = LinearMap.range per₁ := by
  set K₀ := LinearMap.ker (β ∘ₗ r₀)
  set K₁ := LinearMap.ker (β ∘ₗ r₁)
  have hle₀ : LinearMap.range per₀ ≤ K₀ := by
    rintro _ ⟨f, rfl⟩
    exact hv₀ f
  have hle₁ : LinearMap.range per₁ ≤ K₁ := by
    rintro _ ⟨f, rfl⟩
    exact hv₁ f
  have hrange₀ : Module.finrank ℂ (LinearMap.range per₀) = Module.finrank ℂ C :=
    LinearMap.finrank_range_of_inj inj₀
  have hrange₁ : Module.finrank ℂ (LinearMap.range per₁) = Module.finrank ℂ C :=
    LinearMap.finrank_range_of_inj inj₁
  -- the kernel of `β` has dimension `2 dim C`
  have hsurj : LinearMap.range β = ⊤ := by
    obtain ⟨y, hy⟩ : ∃ y, β y ≠ 0 := by
      by_contra h
      push Not at h
      exact hβ (LinearMap.ext h)
    apply eq_top_iff.mpr
    intro z _
    exact ⟨(z / β y) • y, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]⟩
  have hker : Module.finrank ℂ (LinearMap.ker β) = 2 * Module.finrank ℂ C := by
    have h := LinearMap.finrank_range_add_finrank_ker β
    rw [hsurj, finrank_top, Module.finrank_self, hY] at h
    omega
  -- the two kernels embed jointly into the kernel of `β`
  let j : K₀ × K₁ →ₗ[ℂ] Y := (r₀ ∘ₗ K₀.subtype).coprod (r₁ ∘ₗ K₁.subtype)
  have hj : ∀ v, j v ∈ LinearMap.ker β := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    simp only [j, LinearMap.coprod_apply, LinearMap.comp_apply, Submodule.coe_subtype,
      LinearMap.mem_ker, map_add]
    rw [show β (r₀ x) = 0 from hx, show β (r₁ y) = 0 from hy, add_zero]
  have hjinj : Function.Injective (j.codRestrict _ hj) := by
    intro v w hvw
    have h' : j v = j w := congrArg Subtype.val hvw
    have := hinj (a₁ := ((v.1 : X₀), (v.2 : X₁))) (a₂ := ((w.1 : X₀), (w.2 : X₁))) h'
    exact Prod.ext (Subtype.ext (congrArg Prod.fst this)) (Subtype.ext (congrArg Prod.snd this))
  have hsum := LinearMap.finrank_le_finrank_of_injective hjinj
  rw [Module.finrank_prod, hker] at hsum
  have h₀ := Submodule.finrank_mono hle₀
  have h₁ := Submodule.finrank_mono hle₁
  refine ⟨(Submodule.eq_of_le_of_finrank_eq hle₀ ?_).symm,
    (Submodule.eq_of_le_of_finrank_eq hle₁ ?_).symm⟩ <;> omega

/-- An eigenfunctional with eigenvalue `q` kills generalized eigenvectors of any other eigenvalue. -/
theorem functional_eq_zero_of_mem_maxGenEigenspace {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (β : V →ₗ[ℂ] ℂ) (q μ : ℂ) (hβ : ∀ x, β (A x) = q * β x) (hμ : μ ≠ q)
    {x : V} (hx : x ∈ A.maxGenEigenspace μ) : β x = 0 := by
  rw [Module.End.mem_maxGenEigenspace] at hx
  obtain ⟨k, hk⟩ := hx
  have hpow : ∀ (m : ℕ) (y : V), β (((A - μ • 1) ^ m) y) = (q - μ) ^ m * β y := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [pow_succ, Module.End.mul_apply, ih]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        map_smul, hβ, smul_eq_mul]
      ring
  have := hpow k x
  rw [hk, map_zero] at this
  have hq : (q - μ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hμ))
  exact (mul_eq_zero.mp this.symm).resolve_left hq

/-- An injective map intertwining `T` with `s • A` (`s ≠ 0`) pulls generalized eigenvectors of `A`
of eigenvalue `μ` back to generalized eigenvectors of `T` of eigenvalue `s μ`. -/
theorem mem_maxGenEigenspace_of_intertwine {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (per : V →ₗ[ℂ] W) (hper : Function.Injective per)
    (T : Module.End ℂ V) (A : Module.End ℂ W) (s μ : ℂ)
    (hcomm : ∀ f, per (T f) = s • A (per f)) {f : V}
    (hf : per f ∈ A.maxGenEigenspace μ) : f ∈ T.maxGenEigenspace (s * μ) := by
  rw [Module.End.mem_maxGenEigenspace] at hf ⊢
  obtain ⟨k, hk⟩ := hf
  refine ⟨k, hper ?_⟩
  have hone : ∀ g : V, per ((T - (s * μ) • 1) g) = s • (A - μ • 1) (per g) := by
    intro g
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
      map_smul, hcomm, smul_sub, smul_smul]
  have hpow : ∀ (m : ℕ) (g : V),
      per (((T - (s * μ) • 1) ^ m) g) = s ^ m • ((A - μ • 1) ^ m) (per g) := by
    intro m
    induction m with
    | zero => intro g; simp
    | succ m ih =>
      intro g
      rw [pow_succ', Module.End.mul_apply, hone, ih, map_smul, smul_smul, pow_succ',
        pow_succ', Module.End.mul_apply]
  rw [hpow, hk, smul_zero, map_zero]

end Generic

section Concrete

open LevelOneHecke LevelOneEichlerShimura LevelOneESDimension LevelOneHeckeH1

theorem finrank_cuspForm_congr {k k' : ℤ} (h : k = k') :
    Module.finrank ℂ (CuspForm levelOne k) = Module.finrank ℂ (CuspForm levelOne k') := by
  subst h
  rfl

/-- The parity of a twist. -/
def parityOf (σ : ℤ) : Fin 2 := if Even σ then 0 else 1

theorem parityOf_sign (σ : ℤ) : (-1 : ℂ) ^ σ = (-1 : ℂ) ^ (parityOf σ).val := by
  unfold parityOf
  split_ifs with h
  · rw [h.neg_one_zpow]; simp
  · rw [(Int.not_even_iff_odd.mp h).neg_one_zpow]; simp

/-- The weight parameter `h = -(r+1)` of weight `2r + 2`. -/
abbrev hw (r : ℕ) : ℤ := -((r : ℤ) + 1)

theorem weight_eq_r (r : ℕ) : -2 * hw r = ((2 * r : ℕ) : ℤ) + 2 := by push_cast; ring

/-- The level-one period map of weight `2r + 2` into `H¹(GL₂(ℤ), Sym^{2r} ⊗ det^σ)`. -/
abbrev per (r : ℕ) (σ : ℤ) :
    CuspForm levelOne (-2 * hw r) →ₗ[ℂ] groupCohomology.H1 (arithmeticBinaryRep (2 * r) σ) :=
  levelOnePeriodMap (hw r) (2 * r) (weight_eq_r r) (even_two_mul r) σ (parityOf σ) (parityOf_sign σ)

theorem per_injective (r : ℕ) (σ : ℤ) : Function.Injective (per r σ) :=
  levelOnePeriodMap_injective (hw r) (2 * r) (weight_eq_r r) (even_two_mul r) σ (parityOf σ)
    (parityOf_sign σ)

instance cuspForm_fd (r : ℕ) : FiniteDimensional ℂ (CuspForm levelOne (-2 * hw r)) :=
  cuspForm_finiteDimensional (weight_eq_r r) (even_two_mul r)

theorem finrank_modularH1 (r : ℕ) (positive : 0 < r) (τ : ℤ) :
    Module.finrank ℂ (groupCohomology.H1 (modularBinaryRep (2 * r) τ)) =
      2 * Module.finrank ℂ (CuspForm levelOne (-2 * hw r)) + 1 := by
  have h := ModularSymDimension.finrank_H1_sym_eq_cuspForms r positive τ
  rw [finrank_cuspForm_congr (k' := ((2 * r + 2 : ℕ) : ℤ)) (by push_cast; ring)]
  exact h

/-- **Parabolic Eichler–Shimura at level one.** For a nonzero functional `β` on
`H¹(SL₂(ℤ), Sym^{2r})` (`r ≥ 1`) vanishing on the restricted period classes of both twists, the
classes of each twist killed by `β ∘ res` are exactly the period classes. -/
theorem ker_eq_range_period (r : ℕ) (positive : 0 < r) (τ : ℤ)
    (β : groupCohomology.H1 (modularBinaryRep (2 * r) τ) →ₗ[ℂ] ℂ) (hβ : β ≠ 0)
    (hv₀ : ∀ f, β (restriction (2 * r) τ τ (per r τ f)) = 0)
    (hv₁ : ∀ f, β (restriction (2 * r) (τ + 1) τ (per r (τ + 1) f)) = 0) :
    LinearMap.ker (β ∘ₗ restriction (2 * r) τ τ) = LinearMap.range (per r τ) ∧
      LinearMap.ker (β ∘ₗ restriction (2 * r) (τ + 1) τ) = LinearMap.range (per r (τ + 1)) := by
  have := modularH1_finiteDimensional (2 * r) τ
  have := arithmeticH1_finiteDimensional (2 * r) τ
  have := arithmeticH1_finiteDimensional (2 * r) (τ + 1)
  exact ker_eq_range_of_finrank _ _ (restriction_pair_injective (2 * r) τ) β hβ _ _
    (per_injective r τ) (per_injective r (τ + 1)) (finrank_modularH1 r positive τ) hv₀ hv₁

/-- The joint generalized eigenspace of the Hecke operators `T_p` (`p ≠ 3`) on
`H¹(GL₂(ℤ), Sym^d ⊗ det^σ)`. -/
def jointH1 (d : ℕ) (σ : ℤ) (e : Nat.Primes → ℂ) :
    Submodule ℂ (groupCohomology.H1 (arithmeticBinaryRep d σ)) :=
  ⨅ p : {p : Nat.Primes // p.val ≠ 3}, (arithmeticHecke d σ p.1).maxGenEigenspace (e p.1)

/-- **Multiplicity one in level-one `H¹`.** Let `B` be a functional on `H¹(GL₂(ℤ), Sym^{2r} ⊗ det^σ)`
(`r ≥ 1`) whose kernel is the image of the period map and which is an eigenfunctional of some
`T_{p₀}` (`p₀ ≠ 3`) with eigenvalue `q ≠ e_{p₀}`. Then the joint generalized eigenspace of the `T_p`,
`p ≠ 3`, with eigenvalues `e` has dimension at most one. -/
theorem finrank_jointH1_le_one (r : ℕ) (positive : 0 < r) (σ : ℤ)
    (B : groupCohomology.H1 (arithmeticBinaryRep (2 * r) σ) →ₗ[ℂ] ℂ)
    (hker : LinearMap.ker B = LinearMap.range (per r σ)) (e : Nat.Primes → ℂ)
    (p₀ : Nat.Primes) (hp₀ : p₀.val ≠ 3) (q : ℂ)
    (hB : ∀ x, B (arithmeticHecke (2 * r) σ p₀ x) = q * B x) (hq : e p₀ ≠ q) :
    Module.finrank ℂ (jointH1 (2 * r) σ e) ≤ 1 := by
  have hpos : 0 < -2 * hw r := by simp only [hw]; omega
  set J := PeterssonSemisimple.jointGenEigenspaceAwayThree (-2 * hw r)
    (fun p => (p.val : ℂ) ^ σ * e p)
  have hJ : Module.finrank ℂ J ≤ 1 :=
    PeterssonSemisimple.finrank_jointGenEigenspaceAwayThree_le_one _ hpos _
  -- the joint eigenspace lies in the image of `J`
  have hle : jointH1 (2 * r) σ e ≤ J.map (per r σ) := by
    intro x hx
    have hx' : ∀ p : {p : Nat.Primes // p.val ≠ 3},
        x ∈ (arithmeticHecke (2 * r) σ p.1).maxGenEigenspace (e p.1) := by
      intro p
      exact (Submodule.mem_iInf _).mp hx p
    have hBx : B x = 0 :=
      functional_eq_zero_of_mem_maxGenEigenspace _ B q (e p₀) hB hq (hx' ⟨p₀, hp₀⟩)
    have hmem : x ∈ LinearMap.range (per r σ) := by
      rw [← hker]
      exact hBx
    obtain ⟨f, rfl⟩ := hmem
    refine ⟨f, ?_, rfl⟩
    change f ∈ ⨅ p : {p : Nat.Primes // p.val ≠ 3},
      Module.End.maxGenEigenspace (levelOneHecke (-2 * hw r) p.1) ((p.1.val : ℂ) ^ σ * e p.1)
    rw [Submodule.mem_iInf]
    intro p
    exact mem_maxGenEigenspace_of_intertwine (per r σ) (per_injective r σ) _ _ _ _
      (levelOnePeriodMap_hecke (2 * r) σ p.1 (hw r) (weight_eq_r r) (even_two_mul r)
        (parityOf σ) (parityOf_sign σ)) (hx' p)
  calc Module.finrank ℂ (jointH1 (2 * r) σ e) ≤ Module.finrank ℂ (J.map (per r σ)) :=
        Submodule.finrank_mono hle
    _ ≤ Module.finrank ℂ J := Submodule.finrank_map_le _ _
    _ ≤ 1 := hJ

end Concrete

end TernaryPeriodPolynomials.Spectral.ParabolicES
