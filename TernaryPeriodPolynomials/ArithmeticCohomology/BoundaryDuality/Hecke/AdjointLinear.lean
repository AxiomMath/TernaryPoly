module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Data.List.Enum
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


/-!
# Joint generalized eigenspaces of adjoint families of operators

Let `A_i` (`i ∈ ι`) be endomorphisms of a complex vector space `M`, `B_i` endomorphisms of `N`, and
`P : M × N → ℂ` a bilinear pairing with `P(A_i v, w) = P(v, B_i w)`. For characters `c, c' : ι → ℂ`
write `M_c = ⋂_i M(A_i; c_i)` for the joint generalized eigenspace of the family `A`, and `N_{c'}`
likewise.

* **Orthogonality.** `P(M_c, N_{c'}) = 0` unless `c_i = c'_i` for every `i`. For one index `i` with
  `c_i ≠ c'_i`, the claim `P(v, w) = 0` for `(A_i - c_i)^m v = 0`, `(B_i - c'_i)^l w = 0` follows by
  induction on `m + l` from
  `(c'_i - c_i) P(v, w) = P((A_i - c_i) v, w) - P(v, (B_i - c'_i) w)`.
* **Existence of partners.** If `N` is finite dimensional, the `B_i` commute pairwise, and `v ∈ M_c`
  pairs nontrivially with `N`, then `v` pairs nontrivially with some vector of `N_c`: `N` is the sum
  of the joint generalized eigenspaces `N_χ` (`χ : ι → ℂ`), a nonzero functional `P(v, ·)` is
  nonzero on one of them, and by orthogonality that `χ` equals `c`.
* **Eigenfunctionals.** If a functional `φ` on `N` satisfies `φ ∘ B_i = c_i φ` for all `i`, the same
  argument shows that a nonzero `φ` is nonzero on `N_c` (this is the form used when `v` is a genuine
  eigenvector, so that the adjointness relation only gives information about `φ = P(v, ·)`).
* **Affine intertwiners.** A linear map `f` with `f ∘ A = a · f + s · (B ∘ f)` (`s ≠ 0`) carries the
  generalized eigenspace `M(A; μ)` into `M'(B; (μ - a) / s)`, and `M(a + r T; μ) = M(T; (μ - a)/r)`.
  This is the shape of the edge-map formulas `E(T_p y) = E y + p^{-(n+1)} T_p E y` for the local
  Hecke operators at a cusp.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLinear

section Joint

variable {ι M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The joint generalized eigenspace of a family `A` of endomorphisms for the character `c`. -/
def jointSpace (A : ι → Module.End ℂ M) (c : ι → ℂ) : Submodule ℂ M :=
  ⨅ i, (A i).maxGenEigenspace (c i)

/-- Membership in a joint generalized eigenspace is membership in each one. -/
theorem mem_jointSpace_iff {A : ι → Module.End ℂ M} {c : ι → ℂ} {x : M} :
    x ∈ jointSpace A c ↔ ∀ i, x ∈ (A i).maxGenEigenspace (c i) := by
  simp only [jointSpace, Submodule.mem_iInf]

end Joint

section Orthogonality

variable {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-- **One index.** If `P(A v, w) = P(v, B w)` and `a ≠ b`, then `P(v, w) = 0` whenever
`(A - a)^m v = 0` and `(B - b)^l w = 0`. -/
theorem pairing_eq_zero_aux (P : M →ₗ[ℂ] N →ₗ[ℂ] ℂ) (A : Module.End ℂ M) (B : Module.End ℂ N)
    (hadj : ∀ v w, P (A v) w = P v (B w)) {a b : ℂ} (hab : a ≠ b) :
    ∀ (m l : ℕ) (v : M) (w : N), ((A - a • 1) ^ m) v = 0 → ((B - b • 1) ^ l) w = 0 →
      P v w = 0 := by
  intro m
  induction m with
  | zero =>
    intro l v w hv _
    have hv0 : v = 0 := by simpa using hv
    simp [hv0]
  | succ m ih =>
    intro l
    induction l with
    | zero =>
      intro v w _ hw
      have hw0 : w = 0 := by simpa using hw
      simp [hw0]
    | succ l ihl =>
      intro v w hv hw
      have hv' : ((A - a • 1) ^ m) ((A - a • 1) v) = 0 := by
        have h := hv
        rwa [pow_succ (A - a • (1 : Module.End ℂ M)) m, Module.End.mul_apply] at h
      have hw' : ((B - b • 1) ^ l) ((B - b • 1) w) = 0 := by
        have h := hw
        rwa [pow_succ (B - b • (1 : Module.End ℂ N)) l, Module.End.mul_apply] at h
      have h1 : P ((A - a • 1) v) w = 0 := ih (l + 1) _ w hv' hw
      have h2 : P v ((B - b • 1) w) = 0 := ihl v _ hv hw'
      have e1 : P ((A - a • 1) v) w = P v (B w) - a * P v w := by
        simp [hadj]
      have e2 : P v ((B - b • 1) w) = P v (B w) - b * P v w := by
        simp
      rw [e1] at h1
      rw [e2] at h2
      have h3 : (b - a) * P v w = 0 := by linear_combination h1 - h2
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hab
      · exact h

/-- **Orthogonality of joint generalized eigenspaces.** If `P(A_i v, w) = P(v, B_i w)` for all `i`,
then `P(v, w) = 0` for `v` in the joint generalized eigenspace of `c` and `w` in that of `c'`,
unless `c = c'`. -/
theorem jointSpace_pairing_eq_zero (P : M →ₗ[ℂ] N →ₗ[ℂ] ℂ) (A : ι → Module.End ℂ M)
    (B : ι → Module.End ℂ N) (hadj : ∀ i v w, P (A i v) w = P v (B i w)) {c c' : ι → ℂ}
    (hne : ∃ i, c i ≠ c' i) {v : M} (hv : v ∈ jointSpace A c) {w : N}
    (hw : w ∈ jointSpace B c') : P v w = 0 := by
  obtain ⟨i, hi⟩ := hne
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (mem_jointSpace_iff.mp hv i)
  obtain ⟨l, hl⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (mem_jointSpace_iff.mp hw i)
  exact pairing_eq_zero_aux P (A i) (B i) (hadj i) hi m l v w hm hl

/-- **Spectral decomposition.** The joint generalized eigenspaces of a pairwise commuting family of
endomorphisms of a finite-dimensional complex space span it. -/
theorem iSup_jointSpace_eq_top [FiniteDimensional ℂ N] (B : ι → Module.End ℂ N)
    (hcomm : ∀ i j, Commute (B i) (B j)) : ⨆ χ : ι → ℂ, jointSpace B χ = ⊤ :=
  Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo B
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top (B i))

/-- **A pairing partner in the same joint generalized eigenspace.** With `N` finite dimensional, the
`B_i` commuting, and `P(A_i v, w) = P(v, B_i w)`: a vector `v` of the joint generalized eigenspace
of `c` that pairs nontrivially with `N` pairs nontrivially with a vector of the joint generalized
eigenspace of `B` for the same character `c`. -/
theorem exists_mem_jointSpace_pairing_ne_zero [FiniteDimensional ℂ N]
    (P : M →ₗ[ℂ] N →ₗ[ℂ] ℂ) (A : ι → Module.End ℂ M) (B : ι → Module.End ℂ N)
    (hadj : ∀ i v w, P (A i v) w = P v (B i w)) (hcomm : ∀ i j, Commute (B i) (B j))
    {c : ι → ℂ} {v : M} (hv : v ∈ jointSpace A c) (hne : ∃ w, P v w ≠ 0) :
    ∃ w ∈ jointSpace B c, P v w ≠ 0 := by
  by_contra hcon
  obtain ⟨w₀, hw₀⟩ := hne
  have hle : (⨆ χ : ι → ℂ, jointSpace B χ) ≤ LinearMap.ker (P v) := by
    refine iSup_le fun χ => ?_
    intro x hx
    rw [LinearMap.mem_ker]
    by_cases hχ : ∀ i, c i = χ i
    · have hcχ : c = χ := funext hχ
      by_contra hker
      exact hcon ⟨x, by rw [hcχ]; exact hx, hker⟩
    · obtain ⟨i, hi⟩ := not_forall.mp hχ
      exact jointSpace_pairing_eq_zero P A B hadj ⟨i, hi⟩ hv hx
  rw [iSup_jointSpace_eq_top B hcomm] at hle
  exact hw₀ (LinearMap.mem_ker.mp (hle (show w₀ ∈ (⊤ : Submodule ℂ N) from Submodule.mem_top)))

/-- A functional with `φ ∘ B = q φ` kills the generalized eigenspace of `B` for every `μ ≠ q`. -/
theorem functional_eq_zero_of_mem_maxGen (φ : N →ₗ[ℂ] ℂ) (B : Module.End ℂ N) (q μ : ℂ)
    (hφ : ∀ w, φ (B w) = q * φ w) (hμ : q ≠ μ) {w : N} (hw : w ∈ B.maxGenEigenspace μ) :
    φ w = 0 := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hw
  have hpow : ∀ (m : ℕ) (x : N), φ (((B - μ • 1) ^ m) x) = (q - μ) ^ m * φ x := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      have h1 : φ ((B - μ • 1) x) = (q - μ) * φ x := by
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
          map_smul, hφ, smul_eq_mul]
        ring
      rw [pow_succ (B - μ • (1 : Module.End ℂ N)) m, Module.End.mul_apply, ih, h1]
      ring
  have h := hpow k w
  rw [hk, map_zero] at h
  have hne : (q - μ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hμ)
  exact (mul_eq_zero.mp h.symm).resolve_left hne

/-- **An eigenfunctional is nonzero on the matching joint generalized eigenspace.** Let `N` be finite
dimensional with a pairwise commuting family `B_i`, and `φ ≠ 0` a functional with
`φ (B_i w) = c_i φ(w)`. Then `φ` is nonzero on some vector of the joint generalized eigenspace of
`B` for `c`. -/
theorem exists_mem_jointSpace_of_functional [FiniteDimensional ℂ N] (B : ι → Module.End ℂ N)
    (hcomm : ∀ i j, Commute (B i) (B j)) (φ : N →ₗ[ℂ] ℂ) (hφ0 : φ ≠ 0) (c : ι → ℂ)
    (hφ : ∀ i w, φ (B i w) = c i * φ w) : ∃ w ∈ jointSpace B c, φ w ≠ 0 := by
  by_contra hcon
  have hle : (⨆ χ : ι → ℂ, jointSpace B χ) ≤ LinearMap.ker φ := by
    refine iSup_le fun χ => ?_
    intro x hx
    rw [LinearMap.mem_ker]
    by_cases hχ : ∀ i, c i = χ i
    · have hcχ : c = χ := funext hχ
      by_contra hker
      exact hcon ⟨x, by rw [hcχ]; exact hx, hker⟩
    · obtain ⟨i, hi⟩ := not_forall.mp hχ
      exact functional_eq_zero_of_mem_maxGen φ (B i) (c i) (χ i) (hφ i) hi
        (mem_jointSpace_iff.mp hx i)
  rw [iSup_jointSpace_eq_top B hcomm] at hle
  apply hφ0
  ext w
  simpa using LinearMap.mem_ker.mp (hle (show w ∈ (⊤ : Submodule ℂ N) from Submodule.mem_top))

end Orthogonality

section Affine

variable {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-- The generalized eigenspace of `a + r T` for `μ` is that of `T` for `(μ - a) / r` (`r ≠ 0`). -/
theorem maxGenEigenspace_const_add_smul (T : Module.End ℂ M) (a : ℂ) {r : ℂ} (hr : r ≠ 0)
    (μ : ℂ) :
    (a • (1 : Module.End ℂ M) + r • T).maxGenEigenspace μ = T.maxGenEigenspace ((μ - a) / r) := by
  have key : a • (1 : Module.End ℂ M) + r • T - μ • 1 = r • (T - ((μ - a) / r) • 1) := by
    rw [smul_sub, smul_smul, mul_div_cancel₀ _ hr, sub_smul]
    abel
  ext x
  rw [Module.End.mem_maxGenEigenspace, Module.End.mem_maxGenEigenspace]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [key, smul_pow, LinearMap.smul_apply] at hk
    exact (smul_eq_zero.mp hk).resolve_left (pow_ne_zero _ hr)
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [key, smul_pow, LinearMap.smul_apply, hk, smul_zero]

/-- **Affine intertwiners move generalized eigenspaces.** If `f (A v) = a f(v) + s B (f v)` with
`s ≠ 0`, then `f` maps the generalized eigenspace of `A` for `μ` into that of `B` for
`(μ - a) / s`. -/
theorem mem_maxGenEigenspace_map_affine (f : M →ₗ[ℂ] N) (A : Module.End ℂ M)
    (B : Module.End ℂ N) (a s μ : ℂ) (hs : s ≠ 0)
    (hrel : ∀ v, f (A v) = a • f v + s • B (f v)) {v : M} (hv : v ∈ A.maxGenEigenspace μ) :
    f v ∈ B.maxGenEigenspace ((μ - a) / s) := by
  rw [Module.End.mem_maxGenEigenspace] at hv ⊢
  obtain ⟨k, hk⟩ := hv
  refine ⟨k, ?_⟩
  have hone : ∀ w : M, f ((A - μ • 1) w) = s • (B - ((μ - a) / s) • 1) (f w) := by
    intro w
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
      map_smul, hrel, smul_sub, smul_smul]
    rw [mul_div_cancel₀ _ hs, sub_smul]
    abel
  have hpow : ∀ (m : ℕ) (w : M),
      f (((A - μ • 1) ^ m) w) = s ^ m • ((B - ((μ - a) / s) • 1) ^ m) (f w) := by
    intro m
    induction m with
    | zero => intro w; simp
    | succ m ih =>
      intro w
      rw [pow_succ (A - μ • (1 : Module.End ℂ M)) m, Module.End.mul_apply, ih, hone, map_smul,
        smul_smul, pow_succ s m, pow_succ (B - ((μ - a) / s) • (1 : Module.End ℂ N)) m,
        Module.End.mul_apply]
  have h := hpow k v
  rw [hk, map_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hs)

/-- **Joint form of the affine transfer.** -/
theorem map_mem_jointSpace_of_affine (f : M →ₗ[ℂ] N) (A : ι → Module.End ℂ M)
    (B : ι → Module.End ℂ N) (a s c : ι → ℂ) (hs : ∀ i, s i ≠ 0)
    (hrel : ∀ i v, f (A i v) = a i • f v + s i • B i (f v)) {v : M} (hv : v ∈ jointSpace A c) :
    f v ∈ jointSpace B (fun i => (c i - a i) / s i) :=
  mem_jointSpace_iff.mpr fun i =>
    mem_maxGenEigenspace_map_affine f (A i) (B i) (a i) (s i) (c i) (hs i) (hrel i)
      (mem_jointSpace_iff.mp hv i)

end Affine

end TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLinear
