module

public import TernaryPeriodPolynomials.SymmetricSolution.BoundaryObstruction.Rows
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.RowIdentities
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelTransfer.Bridge
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.CohomologySemidirect
public import TernaryPeriodPolynomials.GroupCohomology.Relative.LeviCohomology

@[expose] public section


/-!
# Lemma 4.1 (i), intrinsic form: only the mixed Hochschild-Serre component

Formalized by Claude Sonnet 5.5.  Paper:.

For the bad-line stabilizer `H = U ⋊ L` of `K†` (`U = ⟨U₁₂, U₁₃⟩ ≅ ℤ²` the integral radical `radicalQ`, `L = {±1} × Γ₂` the integral Levi `leviQ`, both inside `GL₃(ℚ)`; `leviQ_normalizes_radicalQ`;
`H` is `TernaryPoly.RelativeVertexCohomology.lineEquiv`'s `HLGroup`), the class `a_F ∈ H²(K†, E_n)` has only the mixed `(1,1)` Hochschild-Serre component:

* `pureRadical_of_pureMixedClass`: `res_U a = 0` (the pure radical component, `E_∞^{0,2} ⊂ H²(U, E)^L`);
* `pureLevi_of_pureMixedClass`: `res_L a = 0` (the pure Levi detection);
* `leviQ_H2_zero`: `H²(L, M) = 0` for every complex `L`-module `M` ("`L` has rational cohomological dimension one", from `RelativeLeviCohomology.line_H2_zero` via `isZero_H2_complex`), so `E_2^{2,0} = H²(L, E^U) = 0` and the filtration step `F²` is zero;
* `pureMixedClass_mathlib`: the same restrictions in Mathlib's group cohomology, through `LevelTransfer.bridge`;
* `lemma41_i_intrinsic`: all of this for the class of any cocycle realizing any path family of a polynomial functional (derived from `lemma41_i_class`, not from a new cocycle choice).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open Matrix TernaryPoly TernaryPoly.RelativeStabilizerParameters TernaryPoly.RelativeStabilizerMatrices

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

/-- The integral radical `U = ⟨U₁₂, U₁₃⟩ ≅ ℤ²` of the bad-line stabilizer, in `GL₃(ℚ)`. -/
def radicalQ : Subgroup RationalGL3 :=
  (TernaryPoly.RadicalFirstCohomologyLattice.lineRadical).map (GeneralLinearGroup.map (Int.castRingHom ℚ))

/-- The integral block-diagonal Levi `L = {±1} × Γ₂` of the bad-line stabilizer, in `GL₃(ℚ)`. -/
def leviQ : Subgroup RationalGL3 :=
  (TernaryPoly.RelativeVertexCohomology.lineLevi.range).map (GeneralLinearGroup.map (Int.castRingHom ℚ))

theorem mem_radicalQ (g : RationalGL3) : g ∈ radicalQ ↔ ∃ s t : ℤ, g = lineUnipotent (s : ℚ) (t : ℚ) := by
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    refine ⟨y.toAdd.1, y.toAdd.2, ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [TernaryPoly.RadicalFirstCohomologyLattice.lineHom, lineElement_val, lineMatrix, upperUnipotent,
        GeneralLinearGroup.map_apply, Matrix.cons_val_two]
  · rintro ⟨s, t, rfl⟩
    refine ⟨TernaryPoly.RadicalFirstCohomologyLattice.lineHom (Multiplicative.ofAdd (s, t)), ⟨_, rfl⟩, ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [TernaryPoly.RadicalFirstCohomologyLattice.lineHom, lineElement_val, lineMatrix, upperUnipotent,
        GeneralLinearGroup.map_apply, Matrix.cons_val_two]

theorem badLineLevi_lineElement (ε : ℤˣ) (D : GL2) (hD : GammaEntries D.val) :
    BadLineLevi (lineElement ε 0 D) := by
  have hk : lineElement ε 0 D ∈ arithmeticLevel := by
    rw [← K3_eq_arithmeticLevel]
    exact ((hl_iff_parameter _).mpr ⟨ε, 0, D, hD, rfl⟩).1
  refine ⟨hk, ?_, ?_, ?_, ?_⟩ <;> simp [lineElement_val, lineMatrix]

theorem mem_leviQ (g : RationalGL3) : g ∈ leviQ ↔ ∃ l : IntegralGL3, BadLineLevi l ∧ g = GeneralLinearGroup.map (Int.castRingHom ℚ) l := by
  constructor
  · rintro ⟨x, ⟨q, rfl⟩, rfl⟩
    exact ⟨_, badLineLevi_lineElement q.1 q.2.val ((mem_Gamma_iff _).mp q.2.property), rfl⟩
  · rintro ⟨l, ⟨hk, h01, h02, h10, h20⟩, rfl⟩
    have hk3 : l ∈ TernaryPoly.RelativeStabilizerCoordinates.K3 := by
      rw [K3_eq_arithmeticLevel]; exact hk
    have hHL : HL l := ⟨hk3, (TernaryPoly.RelativeStabilizerCoordinates.stabilizes_L0_iff l).mpr ⟨h10, h20⟩⟩
    obtain ⟨ε, u, D, hD, rfl⟩ := (hl_iff_parameter l).mp hHL
    have hu : u = 0 := by
      funext i
      fin_cases i
      · simpa [lineElement_val, lineMatrix] using h01
      · simpa [lineElement_val, lineMatrix] using h02
    subst hu
    exact ⟨_, ⟨(ε, ⟨D, (mem_Gamma_iff D).mpr hD⟩), rfl⟩, rfl⟩

open TernaryPeriodPolynomials.Argument.LevelTransfer

theorem radicalQ_le : radicalQ ≤ rationalLevel := by
  intro g hg
  obtain ⟨s, t, rfl⟩ := (mem_radicalQ g).mp hg
  exact TernaryPeriodPolynomials.PolynomialBadLineNormalization.Paths.unipotent_in_level s t

theorem leviQ_le : leviQ ≤ rationalLevel := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := (mem_leviQ g).mp hg
  exact TernaryPeriodPolynomials.PolynomialBadLineNormalization.Paths.integral_in_level l hl.1

/-- The Levi normalizes the radical (so `H = U ⋊ L` has `U` normal and `E^U` is an `L`-module); the semidirect structure itself is
`TernaryPoly.RelativeVertexCohomology.lineEquiv : lineRadical ⋊[lineAction] (ℤˣ × Γ₂) ≃* HLGroup`. -/
theorem leviQ_normalizes_radicalQ {l m : RationalGL3} (hl : l ∈ leviQ) (hm : m ∈ radicalQ) :
    l * m * l⁻¹ ∈ radicalQ := by
  obtain ⟨x, ⟨q, rfl⟩, rfl⟩ := hl
  obtain ⟨y, hy, rfl⟩ := hm
  refine ⟨_, (TernaryPoly.RelativeVertexCohomology.lineAction q ⟨y, hy⟩).2, ?_⟩
  simp [TernaryPoly.RelativeVertexCohomology.lineAction_val]

section Restriction

variable {n : ℕ}

/-- A cocycle whose bar values `c(1, a, ab)` vanish on a subgroup `Δ` restricts to zero in `H²(Δ, E_n)` (model cohomology). -/
theorem resH2_eq_zero_of_bar {Δ : Subgroup RationalGL3} (hΔ : Δ ≤ rationalLevel)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (h : ∀ a b : Δ, c.val.val ![1, (a : RationalGL3), ((a * b : Δ) : RationalGL3)] = 0) :
    resH2 (rationalCoefficientComponent n trivialCharacter) hΔ
      (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0 := by
  have hz : bridgeCocycle (rationalCoefficientComponent n trivialCharacter) Δ
      (cocyclesRes (rationalCoefficientComponent n trivialCharacter) hΔ c) = 0 := by
    apply Subtype.ext
    funext ⟨a, b⟩
    change (bridgeCocycle (rationalCoefficientComponent n trivialCharacter) Δ
      (cocyclesRes (rationalCoefficientComponent n trivialCharacter) hΔ c) : Δ × Δ → HomogeneousPoly n) (a, b) = 0
    rw [bridgeCocycle_apply]
    exact h a b
  apply (bridge (rationalCoefficientComponent n trivialCharacter) Δ).injective
  have h1 : resH2 (rationalCoefficientComponent n trivialCharacter) hΔ
      (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) =
      Submodule.Quotient.mk (cocyclesRes (rationalCoefficientComponent n trivialCharacter) hΔ c) := rfl
  rw [h1, bridge_mk, hz, LinearEquiv.map_zero, map_zero]

/-- **Pure radical part**: a pure-mixed class restricts to zero on the integral radical `U ≅ ℤ²`, in `H²(U, E_n)`. -/
theorem pureRadical_of_pureMixedClass {a : H2 rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (ha : PureMixedClass a) :
    resH2 (rationalCoefficientComponent n trivialCharacter) radicalQ_le a = 0 := by
  obtain ⟨c, rfl, hpm⟩ := ha
  apply resH2_eq_zero_of_bar
  intro x y
  obtain ⟨s, t, hx⟩ := (mem_radicalQ x.1).mp x.2
  obtain ⟨s', t', hy⟩ := (mem_radicalQ y.1).mp y.2
  have := hpm.1 s t s' t'
  rw [show ((x * y : radicalQ) : RationalGL3) = x.1 * y.1 from rfl, hx, hy]
  exact this

/-- **Pure Levi part**: a pure-mixed class restricts to zero on the integral Levi `L = {±1} × Γ₂`, in `H²(L, E_n)`. -/
theorem pureLevi_of_pureMixedClass {a : H2 rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (ha : PureMixedClass a) :
    resH2 (rationalCoefficientComponent n trivialCharacter) leviQ_le a = 0 := by
  obtain ⟨c, rfl, hpm⟩ := ha
  apply resH2_eq_zero_of_bar
  intro x y
  obtain ⟨l, hl, hx⟩ := (mem_leviQ x.1).mp x.2
  obtain ⟨l', hl', hy⟩ := (mem_leviQ y.1).mp y.2
  have := hpm.2 l l' hl hl'
  rw [show ((x * y : leviQ) : RationalGL3) = x.1 * y.1 from rfl, hx, hy, ← map_mul]
  exact this

end Restriction

section Levi

open CategoryTheory Limits

/-- Rational degree-two vanishing implies complex degree-two vanishing (the cocycle and coboundary equations only involve the underlying additive
structure and the action). -/
theorem isZero_H2_complex {G : Type} [Group G] (hQ : ∀ A : Rep ℚ G, IsZero (groupCohomology A 2))
    (B : Rep ℂ G) : IsZero (groupCohomology B 2) := by
  let _ : Module ℚ B.V := Module.compHom B.V (algebraMap ℚ ℂ)
  have : IsScalarTower ℚ ℂ B.V := ⟨fun q c v => by
    change (q • c) • v = (algebraMap ℚ ℂ q) • (c • v)
    rw [Algebra.smul_def, mul_smul]⟩
  let ρQ : Representation ℚ G B.V :=
    { toFun := fun g => (B.ρ g).restrictScalars ℚ
      map_one' := by ext v; simp
      map_mul' := fun g h => by ext v; simp }
  let A : Rep ℚ G := Rep.of ρQ
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ z : groupCohomology B 2, z = 0 from (h x).trans (h y).symm
  intro z
  induction z using groupCohomology.H2_induction_on with
  | h f =>
    have hf : (⇑f : G × G → A.V) ∈ groupCohomology.cocycles₂ A := by
      rw [groupCohomology.mem_cocycles₂_iff]
      exact (groupCohomology.mem_cocycles₂_iff _).mp f.2
    have hz : groupCohomology.H2π A ⟨⇑f, hf⟩ = 0 :=
      (ModuleCat.subsingleton_of_isZero (hQ A)).elim _ _
    rw [groupCohomology.H2π_eq_zero_iff] at hz
    obtain ⟨x, hx⟩ := hz
    rw [groupCohomology.H2π_eq_zero_iff]
    refine ⟨x, ?_⟩
    funext p
    have := congrFun hx p
    simp only [groupCohomology.d₁₂_hom_apply] at this ⊢
    exact this

/-- The Levi `{±1} × Γ₂` of the bad-line stabilizer as matrices in `GL₃(ℚ)`. -/
def leviHom : ℤˣ × Gamma →* RationalGL3 :=
  (GeneralLinearGroup.map (Int.castRingHom ℚ)).comp TernaryPoly.RelativeVertexCohomology.lineLevi

theorem leviHom_injective : Function.Injective leviHom := by
  intro q r h
  have e : ∀ i j, ((lineElement q.1 0 q.2.val).val i j : ℚ) = ((lineElement r.1 0 r.2.val).val i j : ℚ) := fun i j => by
    have := congrArg (fun g : RationalGL3 => g.val i j) h
    simpa [leviHom, TernaryPoly.RelativeVertexCohomology.lineLevi, GeneralLinearGroup.map_apply] using this
  have e' : ∀ i j, (lineElement q.1 0 q.2.val).val i j = (lineElement r.1 0 r.2.val).val i j :=
    fun i j => by exact_mod_cast e i j
  apply Prod.ext
  · apply Units.ext
    simpa [lineElement_val, lineMatrix] using e' 0 0
  · apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [lineElement_val, lineMatrix] using e' 1 1
    · simpa [lineElement_val, lineMatrix] using e' 1 2
    · simpa [lineElement_val, lineMatrix] using e' 2 1
    · simpa [lineElement_val, lineMatrix] using e' 2 2

theorem leviQ_eq_range : leviQ = leviHom.range := by
  unfold leviQ leviHom
  rw [MonoidHom.range_comp]

/-- The group isomorphism `{±1} × Γ₂ ≃ L`. -/
def leviEquiv : ℤˣ × Gamma ≃* leviQ :=
  (MonoidHom.ofInjective leviHom_injective).trans (MulEquiv.subgroupCongr leviQ_eq_range.symm)

/-- **The Levi has rational cohomological dimension one**: `H²(L, M) = 0` for every complex representation `M` of the Levi `L = {±1} × Γ₂` of the bad-line stabilizer
(from the rational vanishing for virtually free groups, `TernaryPoly.RelativeLeviCohomology.line_H2_zero`). -/
theorem leviQ_H2_zero (M : Rep ℂ leviQ) : IsZero (groupCohomology M 2) := by
  have hz := isZero_H2_complex TernaryPoly.RelativeLeviCohomology.line_H2_zero (Rep.res leviEquiv.toMonoidHom M)
  exact hz.of_iso (groupCohomology.mapIso leviEquiv (LinearEquiv.refl ℂ M.V) (fun _ => rfl) 2).symm

end Levi

section Assembly

open CategoryTheory Limits

variable {n : ℕ}

/-- **Mathlib form of the two restrictions**: the images of a pure-mixed class in `H²(U, E_n)` and `H²(L, E_n)` (Mathlib group cohomology, through the bridge) vanish. -/
theorem pureMixedClass_mathlib {a : H2 rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (ha : PureMixedClass a) :
    (groupCohomology.map (Subgroup.inclusion radicalQ_le)
      (resRep (rationalCoefficientComponent n trivialCharacter) radicalQ_le) 2).hom
        (bridge (rationalCoefficientComponent n trivialCharacter) rationalLevel a) = 0 ∧
    (groupCohomology.map (Subgroup.inclusion leviQ_le)
      (resRep (rationalCoefficientComponent n trivialCharacter) leviQ_le) 2).hom
        (bridge (rationalCoefficientComponent n trivialCharacter) rationalLevel a) = 0 := by
  constructor
  · rw [bridge_res, pureRadical_of_pureMixedClass ha, LinearEquiv.map_zero]
  · rw [bridge_res, pureLevi_of_pureMixedClass ha, LinearEquiv.map_zero]

/-- **Lemma 4.1 (i), intrinsic form**.  Let `a_F ∈ H²(K†, E_n)` be the class of any cocycle realizing any path family of a polynomial functional `F`.  Its restriction to the
bad-line stabilizer `H = U ⋊ L` (`U` the integral radical `⟨U₁₂, U₁₃⟩ ≅ ℤ²`, `L = {±1} × Γ₂` the integral Levi) has only the mixed `(1,1)` Hochschild-Serre component:

* the pure radical part vanishes: `res_U a_F = 0` in `H²(U, E_n)` (hence in `H²(U, E_n)^L`);
* the pure Levi part vanishes: `res_L a_F = 0` in `H²(L, E_n)`;
* there is no further filtration term: `H²(L, M) = 0` for every complex `L`-module `M` (rational cohomological dimension one), in particular for `M = E_n^U`, so the `E_2^{2,0}` term (`H²(L, E^U)`) of the spectral sequence of `1 → U → H → L → 1`, and with it the filtration step `F²H²(H, E_n)`, is zero.

Derived from the class-level `lemma41_i_class`, not from a new cocycle choice. -/
theorem lemma41_i_intrinsic {f : HomogeneousPoly n} {F : EdgeChains →ₗ[ℂ] HomogeneousPoly n}
    (hF : IsPolynomialFunctional f F) {τ : rationalLevel → EdgeChains} (hτ : IsPathFamily τ)
    {c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (hc : RealizesPathClass F τ c) :
    resH2 (rationalCoefficientComponent n trivialCharacter) radicalQ_le
        (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0 ∧
      resH2 (rationalCoefficientComponent n trivialCharacter) leviQ_le
        (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0 ∧
      ∀ M : Rep ℂ leviQ, IsZero (groupCohomology M 2) :=
  ⟨pureRadical_of_pureMixedClass (lemma41_i_class hF hτ hc), pureLevi_of_pureMixedClass (lemma41_i_class hF hτ hc),
    leviQ_H2_zero⟩

end Assembly

end TernaryPeriodPolynomials.Argument.Identities
