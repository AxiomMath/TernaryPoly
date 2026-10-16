module

public import TernaryPeriodPolynomials.BoundaryComparison.EichlerShimura
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneCusps
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.FiniteIndexDescent

@[expose] public section


/-!
# Lemma C.3, last sentence: the seeds span the mixed cuspidal groups `𝒞_P(E)` (all plane cusps)

Paper: Lemma C.3 (`ar:lem:seed`),: "Eichler--Shimura theory therefore shows that the holomorphic and antiholomorphic
seeds span `𝒞_P(E)` after including all plane cusps and finite reflections", with `𝒞_R(E)` the
direct sum over faces of type `R` of the subspaces of `H¹(L_R, H¹(N_R, E))` "whose restrictions at
all rational cusps of the binary Levi vanish", injecting into degree-two face
cohomology by Hochschild--Serre.: "Rationally conjugate the finitely
many other plane cusps to `P` and sum the same construction over them."

Everything here is unconditional (it uses `Statements.EichlerShimura.eichler_shimura_spanning_gammaN`
and the level-one and level-three Eichler--Shimura theorems of `Statements.SeedC3`). The plane group
`Γ(N) ∩ P(ℤ)` is the full stabilizer `Γ(N) ∩ P(ℚ)` of the plane, with Levi block exactly `Γ₂(N)`,
only for `N ≥ 3` (the neat case, where there is no finite reflection); the statements about it are
stated for every `N > 0` about the group `Γ(N) ∩ P(ℤ)`, and the assertions about other planes need
`N ≥ 3`.

* `mixed_cuspidal_level_iff`, `seed_span_eq_mixedCuspidal_levelOne`,
  `seed_span_eq_mixedCuspidal_levelThree`: the same for the plane groups `ℤ² ⋊ Λ` with Levi
  `Λ = SL₂(ℤ)` (the plane group of the identity/bad plane of the level-three group) and
  `Λ = Γ₁(3)` (the Levi block of the level-three good plane).
* `mixed_cuspidal_gammaN_iff`: the literal `𝒞_P(E)` (classes of `H¹(Γ₂(N), H¹(Nℤ², E))`
  restricting to zero at the stabilizer of every rational cusp `F · ∞`, `F ∈ GL₂(ℚ)`) consists of the
  classes whose binary coordinate in `H¹(Γ₂(N), Sym^{n+1} ⊗ det⁻¹)` is parabolic.
* `seed_span_eq_mixedCuspidal_gammaN`, `seed_span_eq_mixedCuspidal_H2_gammaN`: the images under the
  Hochschild--Serre edge of the holomorphic and antiholomorphic seeds at `P` span exactly
  `𝒞_P(E)`, and the span of the seed classes in `H²(Γ_P, E)` is the image of `𝒞_P(E)`.
* `seed_span_eq_mixedCuspidal_cusp`, `seed_span_eq_mixedCuspidal_H2_cusp`: the same at the plane
  cusp `h⁻¹ P h`, `h ∈ SL₃(ℤ)`, with the conjugated seeds.
* `seed_span_eq_mixedCuspidal_rational_plane`: every rational plane `g P g⁻¹` is such a cusp, with
  its stabilizer in `Γ(N)`.
* `seed_span_eq_mixedCuspidal_family`: for any family of plane cusps, the direct sum of the cuspidal
  groups is the direct sum of the spans of the seeds.

* `cuspidal_finite_index_descent`: for a finite-index subgroup `Λ ≤ L` of a group acting with a family
  of cusp subgroups, a class of `H¹(L, V)` is mixed cuspidal iff its restriction to `Λ` is (the
  cohomological input of the passage from `Γ₂(N)` to the finite extension `L_P`).

Remaining for the full paper sentence: the finite reflections and the
passage from the neat cover `Γ(N)` to the paper's level-three group, and the comparison of
these Hochschild--Serre mixed cuspidal groups with the Borel--Serre face cohomology of that group.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.MixedCuspidalC3

open scoped MatrixGroups
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument

/-- **`𝒞_P(E)` is the parabolic cohomology (one plane cusp).** A class of
`H¹(Γ₂(N), H¹(Nℤ², E_n))` restricts to zero at the stabilizer of every rational cusp of the binary
Levi `Γ₂(N)` if and only if its coordinate in `H¹(Γ₂(N), Sym^{n+1} ⊗ det⁻¹)` is a parabolic
class. -/
theorem mixed_cuspidal_gammaN_iff (N n : ℕ) [NeZero N]
    (x : groupCohomology.H1
      (splitRadicalH1Representation (SeedC3S4c.gammaNSplitting N) (SeedC3S4c.gammaNRep N n))) :
    x ∈ SeedC3S4c.gammaNCuspidal N n ↔
      ModuleCat.Hom.hom (SeedC3S4c.gammaNLeviIso N n).hom x ∈
        SeedC3S4c.parabolicH1 (CongruenceSubgroup.Gamma N) n :=
  SeedC3S4c.mem_gammaNCuspidal_iff N n x

/-- **Lemma C.3, last sentence, at the plane `P` (unconditional).** For `N ≥ 3` the Hochschild--Serre
edges of the holomorphic and antiholomorphic seeds of cusp forms of weight `n + 3` for `Γ₂(N)` span
exactly the mixed cuspidal group `𝒞_P(E)` of the plane group `Γ(N) ∩ P(ℤ)`. -/
theorem seed_span_eq_mixedCuspidal_gammaN (N n : ℕ) [NeZero N] :
    Submodule.map (splitCohomologyEdge (SeedC3S4c.gammaNSplitting N) (SeedC3S4c.gammaNRep N n))
        (SeedC3S4c.gammaNSeedKerSpan N n) = SeedC3S4c.gammaNCuspidal N n :=
  SeedC3S4c.gammaNSeedKerSpan_map_edge_eq_cuspidal N n
    (EichlerShimura.eichler_shimura_spanning_gammaN N n (Nat.pos_of_ne_zero (NeZero.ne N)))

/-- The same in degree-two cohomology: the span of the complexified de Rham classes of the seeds in
`H²(Γ_P, E_n)` is the image of the mixed cuspidal group (unconditional). -/
theorem seed_span_eq_mixedCuspidal_H2_gammaN (N n : ℕ) [NeZero N] :
    SeedC3S4c.gammaNSeedSpan N n = SeedC3S4c.gammaNCuspidalInH2 N n :=
  SeedC3S4c.gammaNSeedSpan_eq_cuspidalInH2 N n
    (EichlerShimura.eichler_shimura_spanning_gammaN N n (Nat.pos_of_ne_zero (NeZero.ne N)))

/-- **The mixed cuspidal group injects into degree-two face cohomology** (Hochschild--Serre): the edge is injective on the classes with zero radical restriction. -/
theorem mixed_cuspidal_injects_H2 (N n : ℕ) [NeZero N] :
    Function.Injective
      (splitCohomologyEdge (SeedC3S4c.gammaNSplitting N) (SeedC3S4c.gammaNRep N n)) :=
  SeedC3S4c.gammaNEdge_injective N n

/-- **Lemma C.3, last sentence, at the plane cusp `h⁻¹ P h` (unconditional).** The edges of the
conjugated holomorphic and antiholomorphic seeds span the mixed cuspidal group
`𝒞_{h⁻¹Ph}(E)` of the plane group `Γ(N) ∩ h⁻¹ P(ℚ) h`. -/
theorem seed_span_eq_mixedCuspidal_cusp (N n : ℕ) [NeZero N] (h : SL(3, ℤ)) :
    Submodule.map (SeedC3S4c.faceEdge N h n) (SeedC3S4c.faceSeedKerSpan N h n) =
      SeedC3S4c.faceCuspidal N h n :=
  SeedC3S4c.faceSeed_map_edge_eq_cuspidal N h n
    (EichlerShimura.eichler_shimura_spanning_gammaN N n (Nat.pos_of_ne_zero (NeZero.ne N)))

/-- The same in degree-two cohomology of the plane group of the cusp `h⁻¹ P h` (unconditional). -/
theorem seed_span_eq_mixedCuspidal_H2_cusp (N n : ℕ) [NeZero N] (h : SL(3, ℤ)) :
    SeedC3S4c.faceSeedSpan N h n = SeedC3S4c.faceCuspidalInH2 N h n :=
  SeedC3S4c.faceSeedSpan_eq_cuspidalInH2 N h n
    (EichlerShimura.eichler_shimura_spanning_gammaN N n (Nat.pos_of_ne_zero (NeZero.ne N)))

/-- **Every rational plane cusp** `g P g⁻¹`, `g ∈ GL₃(ℚ)`, of `Γ(N)` (`N ≥ 3`) is `h⁻¹ P h` for an
integral `h`, with stabilizer in `Γ(N)` the plane group `Γ_{h⁻¹Ph}`, and the conjugated seeds span
its mixed cuspidal group (unconditional). -/
theorem seed_span_eq_mixedCuspidal_rational_plane (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (g : GL (Fin 3) ℚ) :
    ∃ h : SL(3, ℤ),
      (∀ p ∈ ConvergenceC4.gammaN N,
        ConvergenceC4.InPQ (((g⁻¹ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) *
          ((p : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)) *
          ((g : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)) ↔ p ∈ SeedC3S4c.gammaNPAt N h) ∧
      ∀ n : ℕ, Submodule.map (SeedC3S4c.faceEdge N h n) (SeedC3S4c.faceSeedKerSpan N h n) =
        SeedC3S4c.faceCuspidal N h n := by
  obtain ⟨h, h1, h2⟩ := SeedC3S4c.exists_face_of_rational_plane N hN g
  exact ⟨h, h1, fun n => h2 n (EichlerShimura.eichler_shimura_spanning_gammaN N n (Nat.pos_of_ne_zero (NeZero.ne N)))⟩

/-- **The direct sum over any finite family of plane cusps** `h_i⁻¹ P h_i`: the product of the
mixed cuspidal groups is the product of the edge-images of the conjugated seeds (unconditional).
Taking `h_i` to be representatives of the `Γ(N)`-orbits of rational planes gives the paper's
`𝒞_P(E) = ⊕_{faces} 𝒞_F(E)`. -/
theorem seed_span_eq_mixedCuspidal_family (N n : ℕ) [NeZero N] {ι : Type}
    (h : ι → SL(3, ℤ)) :
    Submodule.pi Set.univ (fun i => Submodule.map (SeedC3S4c.faceEdge N (h i) n)
        (SeedC3S4c.faceSeedKerSpan N (h i) n)) =
      Submodule.pi Set.univ (fun i => SeedC3S4c.faceCuspidal N (h i) n) := by
  congr 1
  funext i
  exact seed_span_eq_mixedCuspidal_cusp N n (h i)


/-! ### The plane groups `ℤ² ⋊ Λ` (radical `ℤ²`, Levi `Λ ⊆ SL₂(ℤ)`) -/

/-- **`𝒞_P(E)` is the parabolic cohomology, for the plane group `ℤ² ⋊ Λ`** (every `Λ ⊆ SL₂(ℤ)`,
including `-1 ∈ Λ`, where `-1` acts on `Sym^{n+1} ⊗ det⁻¹` by `(-1)^{n+1}`). -/
theorem mixed_cuspidal_level_iff (Λ : Subgroup SL(2, ℤ)) (n : ℕ)
    (x : groupCohomology.H1
      (splitRadicalH1Representation (SeedC3S4c.levelSplitting Λ) (SeedC3S4c.levelRep Λ n))) :
    x ∈ SeedC3S4c.levelCuspidal Λ n ↔
      ModuleCat.Hom.hom (SeedC3S4c.levelLeviIso Λ n).hom x ∈ SeedC3S4c.parabolicH1 Λ n :=
  SeedC3S4c.mem_levelCuspidal_iff x

/-- **Lemma C.3, last sentence, at the plane group `ℤ² ⋊ SL₂(ℤ)`** (the identity plane of the
level-three group, level one; unconditional). -/
theorem seed_span_eq_mixedCuspidal_levelOne (n : ℕ) :
    Submodule.map (splitCohomologyEdge (SeedC3S4c.levelSplitting (⊤ : Subgroup SL(2, ℤ)))
        (SeedC3S4c.levelRep (⊤ : Subgroup SL(2, ℤ)) n))
        (SeedC3S4c.seedKerSpan (⊤ : Subgroup SL(2, ℤ)) n) =
      SeedC3S4c.levelCuspidal (⊤ : Subgroup SL(2, ℤ)) n :=
  SeedC3S4c.seedKerSpan_map_edge_eq_levelCuspidal (SeedC3S4c.esSpan_top n)

/-- **Lemma C.3, last sentence, at the plane group `ℤ² ⋊ Γ₁(3)`** (the Levi block `Γ₁(3)` of the
level-three good plane; unconditional). -/
theorem seed_span_eq_mixedCuspidal_levelThree (n : ℕ) :
    Submodule.map (splitCohomologyEdge (SeedC3S4c.levelSplitting (CongruenceSubgroup.Gamma1 3))
        (SeedC3S4c.levelRep (CongruenceSubgroup.Gamma1 3) n))
        (SeedC3S4c.seedKerSpan (CongruenceSubgroup.Gamma1 3) n) =
      SeedC3S4c.levelCuspidal (CongruenceSubgroup.Gamma1 3) n :=
  SeedC3S4c.seedKerSpan_map_edge_eq_levelCuspidal (SeedC3S4c.esSpan_gam3 n)

/-! ### Finite-index descent (the Levi `L_P` versus `Γ₂(N)`) -/

/-- **Finite-index descent of the mixed cuspidal condition.** If `Λ ≤ L` has finite index, a class
`x ∈ H¹(L, V)` vanishes on every cusp subgroup `B i` iff `x|_Λ ∈ H¹(Λ, V)` vanishes on every
`B i ∩ Λ`. (Instance: the Levi of a plane group with reflections and finite congruence quotient
versus its finite-index subgroup acting on the modular curve.) -/
theorem cuspidal_finite_index_descent {L : Type} [Group L] {ι : Type} (B : ι → Subgroup L)
    (V : Rep ℂ L) (Λ : Subgroup L) [Λ.FiniteIndex] (x : groupCohomology.H1 V) :
    x ∈ SeedC3S4c.cuspidalFamily B V ↔
      SeedC3S4c.oneRestriction Λ V x ∈ SeedC3S4c.cuspidalFamily
        (fun i => (B i).comap Λ.subtype) (Rep.res Λ.subtype V) :=
  SeedC3S4c.mem_cuspidalFamily_iff_res B V Λ x

end TernaryPeriodPolynomials.Argument.Statements.MixedCuspidalC3
