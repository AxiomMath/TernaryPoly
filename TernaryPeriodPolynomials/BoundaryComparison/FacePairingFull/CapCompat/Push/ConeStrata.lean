module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeCarriers

@[expose] public section


/-!
# A map of pushout cones that preserves the `L`- and `P`-coordinates induces maps of the three strata

For a chain map `u : K ⟶ K'` between pushout cones sending the `L`-coordinates into the `L'`-coordinates and the
`P`-coordinates into the `P'`-coordinates, the strata maps `uL`, `uP` and the induced map `uA` of the shifted
`A`-coordinate (`iA ≫ u ≫ pA'`) are chain maps (`PushCone.strata`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]
  {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}
  {A' L' P' K' : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a' : A' ⟶ L'} {b' : A' ⟶ P'}

namespace PushCone

variable (𝒞 : PushCone A L P K a b) (𝒟 : PushCone A' L' P' K' a' b')

theorem decomp_zero (z : K.X 0) :
    z = (𝒞.iL 0).hom ((𝒞.pL0).hom z) + (𝒞.iP 0).hom ((𝒞.pP0).hom z) := by
  have h : (𝟙 (K.X 0) : K.X 0 ⟶ K.X 0) = 𝒞.pL0 ≫ 𝒞.iL 0 + 𝒞.pP0 ≫ 𝒞.iP 0 := by
    apply 𝒞.ext0
    · apply Rep.hom_ext; apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro x
      change (𝒞.iL 0).hom x = (𝒞.iL 0).hom ((𝒞.pL0).hom ((𝒞.iL 0).hom x)) +
        (𝒞.iP 0).hom ((𝒞.pP0).hom ((𝒞.iL 0).hom x))
      rw [𝒞.pL0_iL, 𝒞.pP0_iL, map_zero, add_zero]
    · apply Rep.hom_ext; apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro x
      change (𝒞.iP 0).hom x = (𝒞.iL 0).hom ((𝒞.pL0).hom ((𝒞.iP 0).hom x)) +
        (𝒞.iP 0).hom ((𝒞.pP0).hom ((𝒞.iP 0).hom x))
      rw [𝒞.pL0_iP, 𝒞.pP0_iP, map_zero, zero_add]
  exact congrArg (fun φ => φ.hom z) h

theorem decomp_succ (n : ℕ) (z : K.X (n+1)) :
    z = (𝒞.iA n).hom ((𝒞.pA n).hom z) + (𝒞.iL (n+1)).hom ((𝒞.pL n).hom z) +
      (𝒞.iP (n+1)).hom ((𝒞.pP n).hom z) := by
  have h : (𝟙 (K.X (n+1)) : K.X (n+1) ⟶ K.X (n+1)) =
      𝒞.pA n ≫ 𝒞.iA n + 𝒞.pL n ≫ 𝒞.iL (n+1) + 𝒞.pP n ≫ 𝒞.iP (n+1) := by
    apply 𝒞.ext n
    · apply Rep.hom_ext; apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro x
      change (𝒞.iA n).hom x = (𝒞.iA n).hom ((𝒞.pA n).hom ((𝒞.iA n).hom x)) +
        (𝒞.iL (n+1)).hom ((𝒞.pL n).hom ((𝒞.iA n).hom x)) + (𝒞.iP (n+1)).hom ((𝒞.pP n).hom ((𝒞.iA n).hom x))
      rw [𝒞.pA_iA, 𝒞.pL_iA, 𝒞.pP_iA, map_zero, map_zero, add_zero, add_zero]
    · apply Rep.hom_ext; apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro x
      change (𝒞.iL (n+1)).hom x = (𝒞.iA n).hom ((𝒞.pA n).hom ((𝒞.iL (n+1)).hom x)) +
        (𝒞.iL (n+1)).hom ((𝒞.pL n).hom ((𝒞.iL (n+1)).hom x)) +
        (𝒞.iP (n+1)).hom ((𝒞.pP n).hom ((𝒞.iL (n+1)).hom x))
      rw [𝒞.pA_iL, 𝒞.pL_iL, 𝒞.pP_iL, map_zero, map_zero, zero_add, add_zero]
    · apply Rep.hom_ext; apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro x
      change (𝒞.iP (n+1)).hom x = (𝒞.iA n).hom ((𝒞.pA n).hom ((𝒞.iP (n+1)).hom x)) +
        (𝒞.iL (n+1)).hom ((𝒞.pL n).hom ((𝒞.iP (n+1)).hom x)) +
        (𝒞.iP (n+1)).hom ((𝒞.pP n).hom ((𝒞.iP (n+1)).hom x))
      rw [𝒞.pA_iP, 𝒞.pL_iP, 𝒞.pP_iP, map_zero, map_zero, zero_add, zero_add]
  exact congrArg (fun φ => φ.hom z) h

/-- The projection of the degree-`n` term onto its `L`-coordinate. -/
def qL : ∀ n, K.X n ⟶ L.X n
  | 0 => 𝒞.pL0
  | n+1 => 𝒞.pL n

/-- The projection of the degree-`n` term onto its `P`-coordinate. -/
def qP : ∀ n, K.X n ⟶ P.X n
  | 0 => 𝒞.pP0
  | n+1 => 𝒞.pP n

theorem qL_iL (n : ℕ) (l : L.X n) : (𝒞.qL n).hom ((𝒞.iL n).hom l) = l := by
  cases n with
  | zero => exact 𝒞.pL0_iL l
  | succ n => exact 𝒞.pL_iL n l

theorem qP_iP (n : ℕ) (p : P.X n) : (𝒞.qP n).hom ((𝒞.iP n).hom p) = p := by
  cases n with
  | zero => exact 𝒞.pP0_iP p
  | succ n => exact 𝒞.pP_iP n p

theorem pA_d (j : ℕ) (y : K.X (j+2)) :
    (𝒞.pA j).hom ((K.d (j+2) (j+1)).hom y) = -(A.d (j+1) j).hom ((𝒞.pA (j+1)).hom y) := by
  have hy := 𝒞.decomp_succ (j+1) y
  generalize (𝒞.pA (j+1)).hom y = x at hy ⊢
  generalize (𝒞.pL (j+1)).hom y = l at hy
  generalize (𝒞.pP (j+1)).hom y = p at hy
  subst hy
  simp only [map_add]
  rw [𝒞.d_iA_succ, 𝒞.d_iL, 𝒞.d_iP]
  simp only [map_add, map_neg, map_sub, 𝒞.pA_iA, 𝒞.pA_iL, 𝒞.pA_iP]
  simp

variable {𝒞 𝒟}

/-- The `L`-stratum map induced by a chain map of cones, as a family of morphisms. -/
def Lmap (u : K ⟶ K') (n : ℕ) : L.X n ⟶ L'.X n := 𝒞.iL n ≫ u.f n ≫ 𝒟.qL n

/-- The `P`-stratum map induced by a chain map of cones, as a family of morphisms. -/
def Pmap (u : K ⟶ K') (n : ℕ) : P.X n ⟶ P'.X n := 𝒞.iP n ≫ u.f n ≫ 𝒟.qP n

/-- The induced map of the shifted `A`-coordinate. -/
def Amap (u : K ⟶ K') (n : ℕ) : A.X n ⟶ A'.X n := 𝒞.iA n ≫ u.f (n+1) ≫ 𝒟.pA n

theorem iL_injective (n : ℕ) {l l' : L'.X n} (h : (𝒟.iL n).hom l = (𝒟.iL n).hom l') : l = l' := by
  have := congrArg (𝒟.qL n).hom h
  rwa [𝒟.qL_iL, 𝒟.qL_iL] at this

theorem iP_injective (n : ℕ) {p p' : P'.X n} (h : (𝒟.iP n).hom p = (𝒟.iP n).hom p') : p = p' := by
  have := congrArg (𝒟.qP n).hom h
  rwa [𝒟.qP_iP, 𝒟.qP_iP] at this

theorem Lmap_hom (u : K ⟶ K') (n : ℕ) (l : L.X n) :
    (Lmap (𝒞 := 𝒞) (𝒟 := 𝒟) u n).hom l = (𝒟.qL n).hom ((u.f n).hom ((𝒞.iL n).hom l)) := rfl

theorem Pmap_hom (u : K ⟶ K') (n : ℕ) (p : P.X n) :
    (Pmap (𝒞 := 𝒞) (𝒟 := 𝒟) u n).hom p = (𝒟.qP n).hom ((u.f n).hom ((𝒞.iP n).hom p)) := rfl

theorem Amap_hom (u : K ⟶ K') (n : ℕ) (x : A.X n) :
    (Amap (𝒞 := 𝒞) (𝒟 := 𝒟) u n).hom x = (𝒟.pA n).hom ((u.f (n+1)).hom ((𝒞.iA n).hom x)) := rfl

theorem Lmap_spec (u : K ⟶ K') (hL : ∀ n (l : L.X n), ∃ l' : L'.X n, (u.f n).hom ((𝒞.iL n).hom l) = (𝒟.iL n).hom l')
    (n : ℕ) (l : L.X n) :
    (u.f n).hom ((𝒞.iL n).hom l) = (𝒟.iL n).hom ((Lmap (𝒞 := 𝒞) (𝒟 := 𝒟) u n).hom l) := by
  obtain ⟨l', hl'⟩ := hL n l
  rw [Lmap_hom, hl', 𝒟.qL_iL]

theorem Pmap_spec (u : K ⟶ K') (hP : ∀ n (p : P.X n), ∃ p' : P'.X n, (u.f n).hom ((𝒞.iP n).hom p) = (𝒟.iP n).hom p')
    (n : ℕ) (p : P.X n) :
    (u.f n).hom ((𝒞.iP n).hom p) = (𝒟.iP n).hom ((Pmap (𝒞 := 𝒞) (𝒟 := 𝒟) u n).hom p) := by
  obtain ⟨p', hp'⟩ := hP n p
  rw [Pmap_hom, hp', 𝒟.qP_iP]

theorem Lmap_comm (u : K ⟶ K') (hL : ∀ n (l : L.X n), ∃ l' : L'.X n, (u.f n).hom ((𝒞.iL n).hom l) = (𝒟.iL n).hom l')
    (n : ℕ) :
    Lmap (𝒞 := 𝒞) (𝒟 := 𝒟) u (n+1) ≫ L'.d (n+1) n = L.d (n+1) n ≫ Lmap (𝒞 := 𝒞) (𝒟 := 𝒟) u n := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro l
  apply iL_injective (𝒟 := 𝒟) n
  change (𝒟.iL n).hom ((L'.d (n+1) n).hom ((Lmap (𝒞 := 𝒞) (𝒟 := 𝒟) u (n+1)).hom l)) =
    (𝒟.iL n).hom ((Lmap (𝒞 := 𝒞) (𝒟 := 𝒟) u n).hom ((L.d (n+1) n).hom l))
  rw [← 𝒟.d_iL, ← Lmap_spec u hL, ← Lmap_spec u hL, ← 𝒞.d_iL]
  exact congrArg (fun φ => φ.hom ((𝒞.iL (n+1)).hom l)) (u.comm (n+1) n)

theorem Pmap_comm (u : K ⟶ K') (hP : ∀ n (p : P.X n), ∃ p' : P'.X n, (u.f n).hom ((𝒞.iP n).hom p) = (𝒟.iP n).hom p')
    (n : ℕ) :
    Pmap (𝒞 := 𝒞) (𝒟 := 𝒟) u (n+1) ≫ P'.d (n+1) n = P.d (n+1) n ≫ Pmap (𝒞 := 𝒞) (𝒟 := 𝒟) u n := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro p
  apply iP_injective (𝒟 := 𝒟) n
  change (𝒟.iP n).hom ((P'.d (n+1) n).hom ((Pmap (𝒞 := 𝒞) (𝒟 := 𝒟) u (n+1)).hom p)) =
    (𝒟.iP n).hom ((Pmap (𝒞 := 𝒞) (𝒟 := 𝒟) u n).hom ((P.d (n+1) n).hom p))
  rw [← 𝒟.d_iP, ← Pmap_spec u hP, ← Pmap_spec u hP, ← 𝒞.d_iP]
  exact congrArg (fun φ => φ.hom ((𝒞.iP (n+1)).hom p)) (u.comm (n+1) n)

theorem Amap_comm (u : K ⟶ K') (hL : ∀ n (l : L.X n), ∃ l' : L'.X n, (u.f n).hom ((𝒞.iL n).hom l) = (𝒟.iL n).hom l')
    (hP : ∀ n (p : P.X n), ∃ p' : P'.X n, (u.f n).hom ((𝒞.iP n).hom p) = (𝒟.iP n).hom p') (j : ℕ) :
    Amap (𝒞 := 𝒞) (𝒟 := 𝒟) u (j+1) ≫ A'.d (j+1) j = A.d (j+1) j ≫ Amap (𝒞 := 𝒞) (𝒟 := 𝒟) u j := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (A'.d (j+1) j).hom ((𝒟.pA (j+1)).hom ((u.f (j+2)).hom ((𝒞.iA (j+1)).hom x))) =
    (𝒟.pA j).hom ((u.f (j+1)).hom ((𝒞.iA j).hom ((A.d (j+1) j).hom x)))
  have h1 := 𝒟.pA_d j ((u.f (j+2)).hom ((𝒞.iA (j+1)).hom x))
  have h2 : (K'.d (j+2) (j+1)).hom ((u.f (j+2)).hom ((𝒞.iA (j+1)).hom x)) =
      (u.f (j+1)).hom ((K.d (j+2) (j+1)).hom ((𝒞.iA (j+1)).hom x)) :=
    congrArg (fun φ => φ.hom ((𝒞.iA (j+1)).hom x)) (u.comm (j+2) (j+1))
  rw [h2, 𝒞.d_iA_succ] at h1
  obtain ⟨l', hl'⟩ := hL (j+1) ((a.f (j+1)).hom x)
  obtain ⟨p', hp'⟩ := hP (j+1) ((b.f (j+1)).hom x)
  simp only [map_add, map_neg, map_sub, hl', hp', 𝒟.pA_iL, 𝒟.pA_iP] at h1
  have h3 := congrArg Neg.neg h1
  simp only [neg_neg, add_zero, sub_zero] at h3
  rw [← h3]

/-- **Strata maps.**  A chain map of pushout cones preserving the `L`- and `P`-coordinates induces chain maps of the
three strata, compatible with the coordinate inclusions (and the projection to the shifted `A`-coordinate). -/
theorem exists_strata (u : K ⟶ K')
    (hL : ∀ n (l : L.X n), ∃ l' : L'.X n, (u.f n).hom ((𝒞.iL n).hom l) = (𝒟.iL n).hom l')
    (hP : ∀ n (p : P.X n), ∃ p' : P'.X n, (u.f n).hom ((𝒞.iP n).hom p) = (𝒟.iP n).hom p') :
    ∃ (uA : A ⟶ A') (uL : L ⟶ L') (uP : P ⟶ P'),
      (∀ n, uL.f n = 𝒞.iL n ≫ u.f n ≫ 𝒟.qL n) ∧ (∀ n, uP.f n = 𝒞.iP n ≫ u.f n ≫ 𝒟.qP n) ∧
      (∀ n, uA.f n = 𝒞.iA n ≫ u.f (n+1) ≫ 𝒟.pA n) ∧
      (∀ n, 𝒞.iL n ≫ u.f n = uL.f n ≫ 𝒟.iL n) ∧ (∀ n, 𝒞.iP n ≫ u.f n = uP.f n ≫ 𝒟.iP n) := by
  refine ⟨{ f := Amap (𝒞 := 𝒞) (𝒟 := 𝒟) u, comm' := ?_ }, { f := Lmap (𝒞 := 𝒞) (𝒟 := 𝒟) u, comm' := ?_ },
    { f := Pmap (𝒞 := 𝒞) (𝒟 := 𝒟) u, comm' := ?_ }, fun n => rfl, fun n => rfl, fun n => rfl, ?_, ?_⟩
  · rintro i j (rfl : j + 1 = i)
    exact Amap_comm u hL hP j
  · rintro i j (rfl : j + 1 = i)
    exact Lmap_comm u hL j
  · rintro i j (rfl : j + 1 = i)
    exact Pmap_comm u hP j
  · intro n
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro l
    exact Lmap_spec u hL n l
  · intro n
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro p
    exact Pmap_spec u hP n p

end PushCone




end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
