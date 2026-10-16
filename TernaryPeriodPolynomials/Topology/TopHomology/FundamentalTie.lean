module

public import TernaryPeriodPolynomials.Topology.TopHomology.CoinvariantCycle

@[expose] public section


/-!
# Transport of the fundamental cycle along a homotopy equivalence

A chain map of complexes of representations induces maps on coinvariants (`coinvF`) commuting with the
coinvariant differentials; chain homotopic maps agree on degree-four cycles up to boundaries
(`homotopy_cycle`).  Hence for a homotopy equivalence `P ≃ Q` whose target has top cohomology `ℚ`
(with trivial coefficients) and whose source carries a spanning cycle `ω`, the class in `ℚ` of the
transported cocycle `e.inv ≫ c` is a nonzero rational multiple of the evaluation of `c` on `ω`
(`fundamental_tie`).  This ties the fundamental cycle of the model cone to the geometric evaluation on the
fundamental class of the boundary.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.TopHomology

section Tie

variable {Γ : Type} [Group Γ] {P Q R : ChainComplex (Rep.{0} ℚ Γ) ℕ}

/-- The map on coinvariants induced by a chain map. -/
def coinvF (f : P ⟶ Q) (n : ℕ) : (P.X n).ρ.Coinvariants →ₗ[ℚ] (Q.X n).ρ.Coinvariants :=
  Representation.Coinvariants.map _ _ (f.f n).hom

theorem coinvF_mk (f : P ⟶ Q) (n : ℕ) (v : P.X n) :
    coinvF f n (Representation.Coinvariants.mk (P.X n).ρ v) =
      Representation.Coinvariants.mk (Q.X n).ρ ((f.f n).hom v) := rfl

theorem coinvD_mk (P : ChainComplex (Rep.{0} ℚ Γ) ℕ) (i j : ℕ) (v : P.X i) :
    coinvD P i j (Representation.Coinvariants.mk (P.X i).ρ v) =
      Representation.Coinvariants.mk (P.X j).ρ ((P.d i j).hom v) := rfl

theorem coinvF_comp (f : P ⟶ Q) (g : Q ⟶ R) (n : ℕ) :
    coinvF (f ≫ g) n = coinvF g n ∘ₗ coinvF f n := by
  apply Representation.Coinvariants.hom_ext
  rfl

theorem coinvF_id (n : ℕ) : coinvF (𝟙 P) n = LinearMap.id := by
  apply Representation.Coinvariants.hom_ext
  rfl

theorem coinvF_coinvD (f : P ⟶ Q) (i j : ℕ) :
    coinvF f j ∘ₗ coinvD P i j = coinvD Q i j ∘ₗ coinvF f i := by
  apply Representation.Coinvariants.hom_ext
  apply LinearMap.ext
  intro v
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · have h := congrArg (fun m => m.hom v) (f.comm i j)
    change Representation.Coinvariants.mk _ ((f.f j).hom ((P.d i j).hom v)) =
      Representation.Coinvariants.mk _ ((Q.d i j).hom ((f.f i).hom v))
    exact congrArg (Representation.Coinvariants.mk (Q.X j).ρ) h.symm
  · have h1 : P.d i j = 0 := P.shape i j hij
    have h2 : Q.d i j = 0 := Q.shape i j hij
    change Representation.Coinvariants.mk _ ((f.f j).hom ((P.d i j).hom v)) =
      Representation.Coinvariants.mk _ ((Q.d i j).hom ((f.f i).hom v))
    rw [h1, h2]
    simp

theorem coinvHom_chain (f : P ⟶ Q) (n : ℕ) (W : Type) [AddCommGroup W] [Module ℚ W]
    (c : Q.X n ⟶ Rep.trivial ℚ Γ W) :
    coinvHom (P.X n) W (f.f n ≫ c) = coinvHom (Q.X n) W c ∘ₗ coinvF f n :=
  coinvHom_comp (f.f n) W c

theorem homotopy_cycle {f g : P ⟶ Q} (hh : Homotopy f g) (ω : (P.X 4).ρ.Coinvariants)
    (hω : coinvD P 4 3 ω = 0) :
    coinvF f 4 ω - coinvF g 4 ω ∈ LinearMap.range (coinvD Q 5 4) := by
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ ω
  have hc := hh.comm (3 + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hc
  have hv : (f.f 4).hom v = ((P.d 4 3 ≫ hh.hom 3 4).hom v) + ((hh.hom 4 5 ≫ Q.d 5 4).hom v) +
      (g.f 4).hom v := by
    have := congrArg (fun m => m.hom v) hc
    exact this
  have h1 : Representation.Coinvariants.mk (Q.X 4).ρ ((P.d 4 3 ≫ hh.hom 3 4).hom v) = 0 := by
    have h0 : coinvD P 4 3 (Representation.Coinvariants.mk (P.X 4).ρ v) = 0 := hω
    change Representation.Coinvariants.mk (Q.X 4).ρ ((hh.hom 3 4).hom ((P.d 4 3).hom v)) = 0
    have h' : Representation.Coinvariants.map (P.X 3).ρ (Q.X 4).ρ (hh.hom 3 4).hom
        (coinvD P 4 3 (Representation.Coinvariants.mk (P.X 4).ρ v)) = 0 := by
      rw [h0, map_zero]
    exact h'
  refine ⟨Representation.Coinvariants.map (P.X 4).ρ (Q.X 5).ρ (hh.hom 4 5).hom
    (Representation.Coinvariants.mk (P.X 4).ρ v), ?_⟩
  change Representation.Coinvariants.mk (Q.X 4).ρ ((Q.d 5 4).hom ((hh.hom 4 5).hom v)) =
    Representation.Coinvariants.mk (Q.X 4).ρ ((f.f 4).hom v) - Representation.Coinvariants.mk (Q.X 4).ρ ((g.f 4).hom v)
  rw [hv, map_add, map_add, h1, zero_add, add_sub_cancel_right]
  rfl

/-- The morphism of trivial representations induced by a linear map. -/
def trivialMap {W W' : Type} [AddCommGroup W] [Module ℚ W] [AddCommGroup W'] [Module ℚ W']
    (r : W →ₗ[ℚ] W') : Rep.trivial ℚ Γ W ⟶ Rep.trivial ℚ Γ W' :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap (Representation.trivial ℚ Γ W)
    (Representation.trivial ℚ Γ W') r (fun _ _ => rfl))

theorem coinvHom_comp_right {W W' : Type} [AddCommGroup W] [Module ℚ W] [AddCommGroup W']
    [Module ℚ W'] (X : Rep.{0} ℚ Γ) (c : X ⟶ Rep.trivial ℚ Γ W) (r : W →ₗ[ℚ] W')
    (v : X.ρ.Coinvariants) :
    coinvHom X W' (c ≫ trivialMap r) v = r (coinvHom X W c v) := by
  induction v using Representation.Coinvariants.induction_on with
  | h x => rfl

theorem inv_comp_cocycle (e : HomotopyEquiv P Q) (c : P.X 4 ⟶ Rep.trivial ℚ Γ ℚ)
    (hc : P.d 5 4 ≫ c = 0) : Q.d 5 4 ≫ e.inv.f 4 ≫ c = 0 := by
  rw [← Category.assoc, ← e.inv.comm 5 4, Category.assoc, hc, Limits.comp_zero]

theorem coinvHom_eq_zero_of_mem_range (c : P.X 4 ⟶ Rep.trivial ℚ Γ ℚ) (hc : P.d 5 4 ≫ c = 0)
    {u : (P.X 4).ρ.Coinvariants} (hu : u ∈ LinearMap.range (coinvD P 5 4)) :
    coinvHom (P.X 4) ℚ c u = 0 := by
  obtain ⟨w, rfl⟩ := hu
  have h1 := congrArg (fun φ => φ w) (coinvHom_comp (P.d 5 4) ℚ c)
  simp only [hc, map_zero, LinearMap.comp_apply, LinearMap.zero_apply] at h1
  exact h1.symm

/-- **Transport of the fundamental cycle.**  If `P ≃ Q` is a chain homotopy equivalence of complexes of
representations, `ω` spans the degree-four cycles of the coinvariants of `P` and the top cohomology of `Q`
with trivial rational coefficients is `ℚ` (via `geo`), then the class in `ℚ` of the transported cocycle
`e.inv ≫ c` of `Q` is a nonzero rational multiple of the evaluation of `c` on `ω`. -/
theorem fundamental_tie (e : HomotopyEquiv P Q)
    (geo : (Q.linearYonedaObj ℚ (Rep.trivial ℚ Γ ℚ)).homology 4 ≅ ModuleCat.of ℚ ℚ)
    (ω : (P.X 4).ρ.Coinvariants)
    (hcyc : ∀ z : (P.X 4).ρ.Coinvariants, coinvD P 4 3 z = 0 →
      ∃ c : ℚ, z - c • ω ∈ LinearMap.range (coinvD P 5 4)) :
    ∃ κ : ℚ, κ ≠ 0 ∧ ∀ (c : P.X 4 ⟶ Rep.trivial ℚ Γ ℚ) (hc : P.d 5 4 ≫ c = 0),
      cocycleClass (Q.linearYonedaObj ℚ (Rep.trivial ℚ Γ ℚ)) geo (e.inv.f 4 ≫ c)
          (inv_comp_cocycle e c hc) = κ * coinvHom (P.X 4) ℚ c ω := by
  obtain ⟨ωQ, hωQ0, -, hspanQ⟩ := exists_fundamental_cycle Q ⟨geo⟩
  obtain ⟨lam, hlam, hnorm⟩ := fundamental_cycle_normalization Q geo ωQ
    (fun c hc h0 => hspanQ ℚ c hc h0)
  have hz : coinvD P 4 3 (coinvF e.inv 4 ωQ) = 0 := by
    have := LinearMap.congr_fun (coinvF_coinvD e.inv 4 3) ωQ
    simp only [LinearMap.comp_apply] at this
    rw [← this, hωQ0, map_zero]
  obtain ⟨ν, hν⟩ := hcyc _ hz
  have key : ∀ (c : P.X 4 ⟶ Rep.trivial ℚ Γ ℚ), P.d 5 4 ≫ c = 0 →
      coinvHom (P.X 4) ℚ c (coinvF e.inv 4 ωQ) = ν * coinvHom (P.X 4) ℚ c ω := by
    intro c hc
    have h1 := coinvHom_eq_zero_of_mem_range c hc hν
    rw [map_sub, map_smul, sub_eq_zero] at h1
    simpa using h1
  have hν0 : ν ≠ 0 := by
    intro h0
    subst h0
    have hzr : coinvF e.inv 4 ωQ ∈ LinearMap.range (coinvD P 5 4) := by
      simpa using hν
    obtain ⟨w, hw⟩ := hzr
    have hQ1 : coinvF e.hom 4 (coinvF e.inv 4 ωQ) ∈ LinearMap.range (coinvD Q 5 4) := by
      refine ⟨coinvF e.hom 5 w, ?_⟩
      have := LinearMap.congr_fun (coinvF_coinvD e.hom 5 4) w
      simp only [LinearMap.comp_apply] at this
      rw [← this, hw]
    have hQ2 := homotopy_cycle e.homotopyInvHomId ωQ hωQ0
    rw [coinvF_comp, coinvF_id] at hQ2
    have hQ3 : ωQ ∈ LinearMap.range (coinvD Q 5 4) := by
      have := Submodule.sub_mem _ hQ1 hQ2
      simpa using this
    obtain ⟨φ₀, hφ₀, hne⟩ := exists_noncoboundary _ geo
    have h1 := hnorm φ₀ hφ₀
    rw [coinvHom_eq_zero_of_mem_range (φ₀ : Q.X 4 ⟶ Rep.trivial ℚ Γ ℚ) hφ₀ hQ3, mul_zero] at h1
    exact hne h1
  refine ⟨lam * ν, mul_ne_zero hlam hν0, fun c hc => ?_⟩
  rw [hnorm _ (inv_comp_cocycle e c hc), coinvHom_chain e.inv 4 ℚ c, LinearMap.comp_apply,
    key c hc, mul_assoc]

end Tie

end TernaryPeriodPolynomials.Argument.TopHomology
