module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.LowVanishing

@[expose] public section


/-!
# Fiber integration: the cusp cycles define a homomorphism on the Levi

Let `U ≤ Λ` be subgroups of `G` with `H³(U, ℂ) = 0`, and `σ` a two-chain which is a cycle modulo
`U` (the fundamental class of a torus `U ≅ ℤ²`). For an element `m ∈ Λ` normalizing `U` whose
conjugation preserves `σ` up to boundaries modulo `U`, choose `ρ_m` with `∂ρ_m ≡ m⁻¹σm − σ` and put

  `C(m) = P_m σ − ρ_m`,

where `P_m` is the prism operator of right translation by `m`. Given prism and double prism operators
with their homotopy identities (`PrismData`), for every `Λ`-invariant scalar three-cocycle `κ` the
function `m ↦ κ(C(m))` is a homomorphism (`eval_cusp_mul`): the double prism of `σ` relates
`C(h) + C(k)` to `C(hk)`, and the defect `ρ_{hk} − ρ_k − k⁻¹ρ_h k` is a three-cycle modulo `U`,
killed by `H³(U, ℂ) = 0`. In particular `κ(C(f)) = 0` for every `f` of finite order
(`eval_cusp_eq_zero_of_pow`). The cycle `C(m)` is closed modulo every subgroup containing `U` and
`m` (`boundary_cusp_mem_null`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.ChiHom

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.TopVanishing
  (homogeneousBoundary homogeneousBoundary_single lin_ext_single)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus
open TernaryPeriodPolynomials.BoundaryDuality.ChainDuality
open TernaryPeriodPolynomials.BoundaryDuality.LowVanishing

variable {G : Type} [Group G]

section Conjugation

/-- Conjugation of all vertices: `x ↦ m⁻¹ x m`. -/
def conjugate (m : G) (k : ℕ) : Chains G k →ₗ[ℂ] Chains G k :=
  Finsupp.lmapDomain ℂ ℂ (fun x i => m⁻¹ * x i * m)

theorem conjugate_single (m : G) {k : ℕ} (x : Fin (k + 1) → G) (a : ℂ) :
    conjugate m k (Finsupp.single x a) = Finsupp.single (fun i => m⁻¹ * x i * m) a := by
  rw [conjugate, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- Right translation is left translation after conjugation. -/
theorem rightTranslate_eq (m : G) (k : ℕ) (c : Chains G k) :
    rightTranslate m k c = leftTranslate m k (conjugate m k c) := by
  have h : rightTranslate m k = leftTranslate m k ∘ₗ conjugate m k :=
    lin_ext_single fun x => by
      rw [LinearMap.comp_apply, rightTranslate_single, conjugate_single, leftTranslate_single]
      congr 1
      funext i
      group
  exact LinearMap.congr_fun h c

/-- Conjugation commutes with the boundary. -/
theorem boundary_conjugate (m : G) (k : ℕ) (c : Chains G (k + 1)) :
    homogeneousBoundary (k + 1) (conjugate m (k + 1) c) =
      conjugate m k (homogeneousBoundary (k + 1) c) := by
  have h : homogeneousBoundary (k + 1) ∘ₗ conjugate m (k + 1) =
      conjugate m k ∘ₗ homogeneousBoundary (G := G) (k + 1) :=
    lin_ext_single fun x => by
      have hface : ∀ i, (fun j => m⁻¹ * x j * m) ∘ Fin.succAbove i =
          fun j => m⁻¹ * (x ∘ Fin.succAbove i) j * m := fun _ => rfl
      rw [LinearMap.comp_apply, LinearMap.comp_apply, conjugate_single, homogeneousBoundary_single,
        homogeneousBoundary_single]
      simp only [map_sum, map_smul, conjugate_single, hface]
  exact LinearMap.congr_fun h c

/-- Conjugation twice is conjugation by the product. -/
theorem conjugate_conjugate (h k : G) (n : ℕ) (c : Chains G n) :
    conjugate k n (conjugate h n c) = conjugate (h * k) n c := by
  have e : conjugate k n ∘ₗ conjugate h n = conjugate (G := G) (h * k) n :=
    lin_ext_single fun x => by
      rw [LinearMap.comp_apply, conjugate_single, conjugate_single, conjugate_single]
      congr 1
      funext i
      group
  exact LinearMap.congr_fun e c

/-- Conjugation by an element normalizing `U` preserves the `U`-null chains. -/
theorem conjugate_mem_null {U : Subgroup G} {m : G} (hm : ∀ u ∈ U, m⁻¹ * u * m ∈ U) {k : ℕ}
    {c : Chains G k} (hc : c ∈ NullChains U k) : conjugate m k c ∈ NullChains U k := by
  have hle : NullChains U k ≤ (NullChains U k).comap (conjugate m k) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, x, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, conjugate_single, conjugate_single]
    refine Submodule.subset_span ⟨⟨m⁻¹ * γ.val * m, hm γ.val γ.property⟩, fun i => m⁻¹ * x i * m, ?_⟩
    congr 2
    funext i
    show m⁻¹ * (γ.val * x i) * m = (m⁻¹ * γ.val * m) * (m⁻¹ * x i * m)
    group
  exact hle hc

/-- Conjugation by an element normalizing `U` preserves the boundaries modulo `U`. -/
theorem conjugate_mem_bdry {U : Subgroup G} {m : G} (hm : ∀ u ∈ U, m⁻¹ * u * m ∈ U) {k : ℕ}
    {c : Chains G k} (hc : c ∈ BdryChains U k) : conjugate m k c ∈ BdryChains U k := by
  obtain ⟨n, hn, d, hd, rfl⟩ := Submodule.mem_sup.mp hc
  obtain ⟨e, rfl⟩ := LinearMap.mem_range.mp hd
  rw [map_add, ← boundary_conjugate]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (conjugate_mem_null hm hn))
    (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))

end Conjugation

section Evaluation

/-- Null chains of a subgroup are null chains of every larger subgroup. -/
theorem nullChains_mono {U Λ : Subgroup G} (h : U ≤ Λ) (k : ℕ) :
    NullChains U k ≤ NullChains Λ k := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨γ, x, rfl⟩
  exact Submodule.subset_span ⟨⟨γ.val, h γ.property⟩, x, rfl⟩

/-- Left translation by an element of `Λ` differs from the identity by a null chain. -/
theorem leftTranslate_sub_mem {Λ : Subgroup G} {g : G} (hg : g ∈ Λ) {k : ℕ} (c : Chains G k) :
    leftTranslate g k c - c ∈ NullChains Λ k := by
  refine Finsupp.induction_linear c ?_ (fun c c' hc hc' => ?_) (fun x a => ?_)
  · simp
  · rw [map_add, add_sub_add_comm]
    exact Submodule.add_mem _ hc hc'
  · rw [leftTranslate_single]
    have hs : Finsupp.single (fun i => g * x i) a - Finsupp.single x a =
        a • (Finsupp.single (fun i => g * x i) 1 - Finsupp.single x 1) := by
      rw [smul_sub, Finsupp.smul_single_one, Finsupp.smul_single_one]
    rw [hs]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨⟨g, hg⟩, x, rfl⟩)

/-- A boundary modulo null chains has a filling chain, in every dimension. -/
theorem exists_fill' {Λ : Subgroup G} {k : ℕ} {c : Chains G k} (hc : c ∈ BdryChains Λ k) :
    ∃ D : Chains G (k + 1), c - homogeneousBoundary (k + 1) D ∈ NullChains Λ k := by
  obtain ⟨n, hn, d, hd, rfl⟩ := Submodule.mem_sup.mp hc
  obtain ⟨e, rfl⟩ := LinearMap.mem_range.mp hd
  exact ⟨e, by rwa [add_sub_cancel_right]⟩

end Evaluation

/-- Prism and double prism operators with their homotopy identities: `P_h` in dimensions one to
three with `∂P_h + P_h∂ = R_h − id`, and the double prism `Q_{h,k}` on one- and two-chains with
`∂Q_{h,k} = Q_{h,k}∂ + P_k R_h − P_{hk} + P_h`; all commute with left translations and preserve
null chains. -/
structure PrismData (G : Type) [Group G] where
  /-- The prism on one-chains. -/
  P1 : G → Chains G 1 →ₗ[ℂ] Chains G 2
  /-- The prism on two-chains. -/
  P2 : G → Chains G 2 →ₗ[ℂ] Chains G 3
  /-- The prism on three-chains. -/
  P3 : G → Chains G 3 →ₗ[ℂ] Chains G 4
  /-- The double prism on one-chains. -/
  Q1 : G → G → Chains G 1 →ₗ[ℂ] Chains G 3
  /-- The double prism on two-chains. -/
  Q2 : G → G → Chains G 2 →ₗ[ℂ] Chains G 4
  prism_two : ∀ h c, homogeneousBoundary 3 (P2 h c) + P1 h (homogeneousBoundary 2 c) =
    rightTranslate h 2 c - c
  prism_three : ∀ h c, homogeneousBoundary 4 (P3 h c) + P2 h (homogeneousBoundary 3 c) =
    rightTranslate h 3 c - c
  dprism_two : ∀ h k c, homogeneousBoundary 4 (Q2 h k c) =
    Q1 h k (homogeneousBoundary 2 c) + P2 k (rightTranslate h 2 c) - P2 (h * k) c + P2 h c
  P2_left : ∀ h g c, P2 h (leftTranslate g 2 c) = leftTranslate g 3 (P2 h c)
  P1_null : ∀ (Λ : Subgroup G) h c, c ∈ NullChains Λ 1 → P1 h c ∈ NullChains Λ 2
  P2_null : ∀ (Λ : Subgroup G) h c, c ∈ NullChains Λ 2 → P2 h c ∈ NullChains Λ 3
  Q1_null : ∀ (Λ : Subgroup G) h k c, c ∈ NullChains Λ 1 → Q1 h k c ∈ NullChains Λ 3

section Cusp

variable (D : PrismData G) {Λ U : Subgroup G} (σ : Chains G 2)

/-- The Levi elements for the torus chain `σ`: elements of `Λ` normalizing `U` whose conjugation
preserves `σ` up to boundaries modulo `U`. -/
def IsLevi (Λ U : Subgroup G) (σ : Chains G 2) (m : G) : Prop :=
  m ∈ Λ ∧ (∀ u ∈ U, m⁻¹ * u * m ∈ U) ∧ conjugate m 2 σ - σ ∈ BdryChains U 2

/-- The chosen correction `ρ_m` with `∂ρ_m ≡ m⁻¹σm − σ` modulo `U`. -/
def rho {m : G} (hm : IsLevi Λ U σ m) : Chains G 3 :=
  Classical.choose (exists_fill' hm.2.2)

theorem rho_spec {m : G} (hm : IsLevi Λ U σ m) :
    conjugate m 2 σ - σ - homogeneousBoundary 3 (rho σ hm) ∈ NullChains U 2 :=
  Classical.choose_spec (exists_fill' hm.2.2)

/-- The cusp cycle `C(m) = P_m σ − ρ_m`. -/
def cusp {m : G} (hm : IsLevi Λ U σ m) : Chains G 3 :=
  D.P2 m σ - rho σ hm

/-- The cusp cycle is closed modulo every subgroup containing `U` and `m`. -/
theorem boundary_cusp_mem_null {Λ' : Subgroup G} (hUΛ' : U ≤ Λ')
    (hσ : homogeneousBoundary 2 σ ∈ NullChains U 1) {m : G} (hm : IsLevi Λ U σ m)
    (hmΛ' : m ∈ Λ') : homogeneousBoundary 3 (cusp D σ hm) ∈ NullChains Λ' 2 := by
  have hP := D.prism_two m σ
  have hn := nullChains_mono hUΛ' 2 (rho_spec σ hm)
  have hL := leftTranslate_sub_mem hmΛ' (conjugate m 2 σ)
  have hP1 := nullChains_mono hUΛ' 2 (D.P1_null U m _ hσ)
  have hP' : homogeneousBoundary 3 (D.P2 m σ) =
      leftTranslate m 2 (conjugate m 2 σ) - σ - D.P1 m (homogeneousBoundary 2 σ) := by
    rw [← rightTranslate_eq]
    exact eq_sub_of_add_eq hP
  have key : homogeneousBoundary 3 (cusp D σ hm) =
      (leftTranslate m 2 (conjugate m 2 σ) - conjugate m 2 σ) +
        (conjugate m 2 σ - σ - homogeneousBoundary 3 (rho σ hm)) -
        D.P1 m (homogeneousBoundary 2 σ) := by
    rw [cusp, map_sub, hP']
    abel
  rw [key]
  exact Submodule.sub_mem _ (Submodule.add_mem _ hL hn) hP1

variable {σ}

/-- **Fiber integration is a homomorphism.** For a `Λ`-invariant scalar three-cocycle `κ`,
`κ(C(hk)) = κ(C(h)) + κ(C(k))`. -/
theorem eval_cusp_mul (hUΛ : U ≤ Λ) (hU : TopVanishingThree U)
    (hσ : homogeneousBoundary 2 σ ∈ NullChains U 1) (κ : (Fin 4 → G) → ℂ)
    (hκ : ∀ (γ : Λ) x, κ (fun i => γ.val * x i) = κ x) (closed : ∀ x, differentialThreeRaw κ x = 0)
    {h k : G} (hh : IsLevi Λ U σ h) (hk : IsLevi Λ U σ k) (hhk : IsLevi Λ U σ (h * k)) :
    Finsupp.linearCombination ℂ κ (cusp D σ hhk) =
      Finsupp.linearCombination ℂ κ (cusp D σ hh) + Finsupp.linearCombination ℂ κ (cusp D σ hk) := by
  set ev := Finsupp.linearCombination ℂ κ
  have hκU : ∀ (γ : U) x, κ (fun i => γ.val * x i) = κ x := fun γ x => hκ ⟨γ.val, hUΛ γ.property⟩ x
  -- the evaluation kills boundaries, null chains and left translations by `Λ`
  have evBdry : ∀ X : Chains G 4, ev (homogeneousBoundary 4 X) = 0 := fun X =>
    (mem_bdryChains_iff Λ _).mp (Submodule.mem_sup_right (LinearMap.mem_range_self _ X)) κ hκ closed
  have evNullU : ∀ c, c ∈ NullChains U 3 → ev c = 0 := fun c hc => eval_null κ hκU hc
  have evLeft : ∀ g ∈ Λ, ∀ c, ev (leftTranslate g 3 c) = ev c := fun g hg c => by
    have := eval_null κ hκ (leftTranslate_sub_mem hg c)
    rw [map_sub, sub_eq_zero] at this
    exact this
  -- the double prism identity, evaluated
  have hQ := congrArg ev (D.dprism_two h k σ)
  rw [evBdry, map_add, map_sub, map_add] at hQ
  have q1 : ev (D.Q1 h k (homogeneousBoundary 2 σ)) = 0 := evNullU _ (D.Q1_null U h k _ hσ)
  -- `P_k R_h σ = h · P_k (h⁻¹σh)` and `h⁻¹σh = σ + ∂ρ_h + n_h`
  have hR : D.P2 k (rightTranslate h 2 σ) = leftTranslate h 3 (D.P2 k (conjugate h 2 σ)) := by
    rw [rightTranslate_eq, D.P2_left]
  set nh := conjugate h 2 σ - σ - homogeneousBoundary 3 (rho σ hh) with hnh
  have hconj : conjugate h 2 σ = σ + homogeneousBoundary 3 (rho σ hh) + nh := by
    rw [hnh]; abel
  have pnull : ev (D.P2 k nh) = 0 := evNullU _ (D.P2_null U k _ (rho_spec σ hh))
  have hP3 := D.prism_three k (rho σ hh)
  have pbd : D.P2 k (homogeneousBoundary 3 (rho σ hh)) =
      rightTranslate k 3 (rho σ hh) - rho σ hh - homogeneousBoundary 4 (D.P3 k (rho σ hh)) := by
    rw [← hP3]; abel
  have evR : ev (rightTranslate k 3 (rho σ hh)) = ev (conjugate k 3 (rho σ hh)) := by
    rw [rightTranslate_eq, evLeft k hk.1]
  have term : ev (D.P2 k (rightTranslate h 2 σ)) =
      ev (D.P2 k σ) + ev (conjugate k 3 (rho σ hh)) - ev (rho σ hh) := by
    rw [hR, evLeft h hh.1, hconj, map_add, map_add, map_add, map_add, pnull, pbd, map_sub, map_sub,
      evBdry, evR]
    ring
  -- the defect of the corrections is a cycle modulo `U`, hence killed
  set Z := rho σ hhk - rho σ hk - conjugate k 3 (rho σ hh) with hZ
  have hZcycle : homogeneousBoundary 3 Z ∈ NullChains U 2 := by
    have e : homogeneousBoundary 3 Z =
        conjugate k 2 (conjugate h 2 σ - σ - homogeneousBoundary 3 (rho σ hh)) +
          (conjugate k 2 σ - σ - homogeneousBoundary 3 (rho σ hk)) -
          (conjugate (h * k) 2 σ - σ - homogeneousBoundary 3 (rho σ hhk)) := by
      rw [hZ]
      simp only [map_sub]
      rw [boundary_conjugate, conjugate_conjugate]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.add_mem _ (conjugate_mem_null hk.2.1 (rho_spec σ hh))
      (rho_spec σ hk)) (rho_spec σ hhk)
  have evZ : ev Z = 0 :=
    (mem_bdryChains_iff U Z).mp (mem_bdryChains_of_cycle hU hZcycle) κ hκU closed
  rw [hZ, map_sub, map_sub] at evZ
  simp only [cusp, map_sub]
  rw [q1, term] at hQ
  linear_combination hQ - evZ

/-- The identity is a Levi element. -/
theorem isLevi_one : IsLevi Λ U σ 1 := by
  refine ⟨Λ.one_mem, fun u hu => by simpa using hu, ?_⟩
  have h1 : conjugate (1 : G) 2 = LinearMap.id :=
    lin_ext_single fun x => by
      rw [conjugate_single, LinearMap.id_apply]
      congr 1
      funext i
      group
  rw [h1, LinearMap.id_apply, sub_self]
  exact Submodule.zero_mem _

/-- Levi elements are closed under products. -/
theorem IsLevi.mul {h k : G} (hh : IsLevi Λ U σ h) (hk : IsLevi Λ U σ k) :
    IsLevi Λ U σ (h * k) := by
  refine ⟨Λ.mul_mem hh.1 hk.1, fun u hu => ?_, ?_⟩
  · have e : (h * k)⁻¹ * u * (h * k) = k⁻¹ * (h⁻¹ * u * h) * k := by group
    rw [e]
    exact hk.2.1 _ (hh.2.1 u hu)
  · have e : conjugate (h * k) 2 σ - σ =
        conjugate k 2 (conjugate h 2 σ - σ) + (conjugate k 2 σ - σ) := by
      rw [map_sub, conjugate_conjugate]
      abel
    rw [e]
    exact Submodule.add_mem _ (conjugate_mem_bdry hk.2.1 hh.2.2) hk.2.2

/-- Powers of a Levi element are Levi elements. -/
theorem IsLevi.pow {f : G} (hf : IsLevi Λ U σ f) (n : ℕ) : IsLevi Λ U σ (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact isLevi_one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

/-- The cusp cycle only depends on the element. -/
theorem cusp_congr {m m' : G} (e : m = m') (hm : IsLevi Λ U σ m) (hm' : IsLevi Λ U σ m') :
    cusp D σ hm = cusp D σ hm' := by
  subst e
  rfl

/-- **Torsion Levi elements have vanishing fiber integral.** -/
theorem eval_cusp_eq_zero_of_pow (hUΛ : U ≤ Λ) (hU : TopVanishingThree U)
    (hσ : homogeneousBoundary 2 σ ∈ NullChains U 1) (κ : (Fin 4 → G) → ℂ)
    (hκ : ∀ (γ : Λ) x, κ (fun i => γ.val * x i) = κ x) (closed : ∀ x, differentialThreeRaw κ x = 0)
    {f : G} (hf : IsLevi Λ U σ f) {n : ℕ} (hn : 0 < n) (hfn : f ^ n = 1) :
    Finsupp.linearCombination ℂ κ (cusp D σ hf) = 0 := by
  have one : Finsupp.linearCombination ℂ κ (cusp D σ (isLevi_one (Λ := Λ) (U := U) (σ := σ))) =
      0 := by
    have h1 := eval_cusp_mul D hUΛ hU hσ κ hκ closed (isLevi_one (Λ := Λ) (U := U) (σ := σ))
      isLevi_one (isLevi_one.mul isLevi_one)
    rw [cusp_congr D (mul_one (1 : G)) (isLevi_one.mul isLevi_one) isLevi_one] at h1
    linear_combination -h1
  have hpow : ∀ j : ℕ, Finsupp.linearCombination ℂ κ (cusp D σ (hf.pow j)) =
      j * Finsupp.linearCombination ℂ κ (cusp D σ hf) := by
    intro j
    induction j with
    | zero =>
      rw [cusp_congr D (pow_zero f) (hf.pow 0) isLevi_one, one, Nat.cast_zero, zero_mul]
    | succ j ih =>
      rw [cusp_congr D (pow_succ f j) (hf.pow (j + 1)) ((hf.pow j).mul hf),
        eval_cusp_mul D hUΛ hU hσ κ hκ closed (hf.pow j) hf ((hf.pow j).mul hf), ih]
      push_cast
      ring
  have hn' := hpow n
  rw [cusp_congr D hfn (hf.pow n) isLevi_one, one] at hn'
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  exact (mul_eq_zero.mp hn'.symm).resolve_left hnc

end Cusp

end TernaryPeriodPolynomials.BoundaryDuality.ChiHom
