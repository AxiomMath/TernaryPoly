module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Rational.FiberEquivariance

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryRationalFiber
open SymmetricOddRationalSeed SymmetricOddRationalTower
open OrdinaryCovectors OrdinaryCovectorOrbits OrdinaryPolynomialNorm
open OrdinaryFiberPermutations OrdinarySignedFibers OrdinarySeedEquivariance

theorem fracPerm_mul (π σ : Equiv.Perm (Fin 3)) (x : Frac) :
    fracPerm σ (fracPerm π x)=fracPerm (π*σ) x := by
  have he : (fracPerm σ).toAlgHom.comp (fracPerm π).toAlgHom=(fracPerm (π*σ)).toAlgHom := by
    apply fraction_ext
    intro p
    change fracPerm σ (fracPerm π (embed p))=fracPerm (π*σ) (embed p)
    rw [fracPerm_embed,fracPerm_embed,fracPerm_embed]
    exact congrArg embed (DFunLike.congr_fun (permutePoly_mul π σ) p)
  exact DFunLike.congr_fun he x

theorem fracPerm_one (x : Frac) : fracPerm 1 x=x := by
  have he : (fracPerm 1).toAlgHom=AlgHom.id ℚ Frac := by
    apply fraction_ext
    intro p
    change fracPerm 1 (embed p)=embed p
    rw [fracPerm_embed,permutePoly_one,AlgHom.id_apply]
  exact DFunLike.congr_fun he x

theorem fracPerm_swap (x : Frac) : fracPerm swapPerm x=fracS x := by
  have he : (fracPerm swapPerm).toAlgHom=fracS.toAlgHom := by
    apply fraction_ext
    intro p
    change fracPerm swapPerm (embed p)=fracS (embed p)
    rw [fracPerm_embed,fracS_embed,permutePoly_swap]
  exact DFunLike.congr_fun he x

theorem fracPerm_cycle (x : Frac) : fracPerm cyclePerm x=fracC x := by
  have he : (fracPerm cyclePerm).toAlgHom=fracC.toAlgHom := by
    apply fraction_ext
    intro p
    change fracPerm cyclePerm (embed p)=fracC (embed p)
    rw [fracPerm_embed,fracC_embed,permutePoly_cycle]
  exact DFunLike.congr_fun he x

theorem signPoly_singleton (i : Fin 3) : signPoly {i}=flipPoly i := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [signPoly,flipPoly]

theorem fracFlip_conjugate (i : Fin 3) (x : Frac) :
    fracPerm (Equiv.swap i 2) (fracD3 (fracPerm (Equiv.swap i 2) x))=fracSign {i} x := by
  have he : (fracPerm (Equiv.swap i 2)).toAlgHom.comp
      (fracD3.toAlgHom.comp (fracPerm (Equiv.swap i 2)).toAlgHom)=(fracSign {i}).toAlgHom := by
    apply fraction_ext
    intro p
    change fracPerm (Equiv.swap i 2) (fracD3 (fracPerm (Equiv.swap i 2) (embed p)))=
      fracSign {i} (embed p)
    rw [fracPerm_embed,fracD3_embed,fracPerm_embed,fracSign_embed,signPoly_singleton]
    exact congrArg embed (DFunLike.congr_fun (flipPoly_conjugate i) p)
  exact DFunLike.congr_fun he x

theorem fracSign_insert (s : Finset (Fin 3)) (i : Fin 3) (hi : i∉s) (x : Frac) :
    fracSign {i} (fracSign s x)=fracSign (insert i s) x := by
  have he : (fracSign {i}).toAlgHom.comp (fracSign s).toAlgHom=(fracSign (insert i s)).toAlgHom := by
    apply fraction_ext
    intro p
    change fracSign {i} (fracSign s (embed p))=fracSign (insert i s) (embed p)
    rw [fracSign_embed,fracSign_embed,fracSign_embed,signPoly_singleton]
    exact congrArg embed (DFunLike.congr_fun (signPoly_insert s i hi) p)
  exact DFunLike.congr_fun he x

theorem fracSign_empty (x : Frac) : fracSign ∅ x=x := by
  have he : (fracSign ∅).toAlgHom=AlgHom.id ℚ Frac := by
    apply fraction_ext
    intro p
    change fracSign ∅ (embed p)=embed p
    rw [fracSign_embed,signPoly_empty,AlgHom.id_apply]
  exact DFunLike.congr_fun he x

/-- The actual fraction-field generator equations imply every permutation equation. -/
theorem permutation_equivariance (F : Covector → Frac)
    (hs : ∀ r,F (swapRow r)=fracS (F r))
    (hc : ∀ r,F (cycleRow r)=fracC (F r)) :
    ∀ π r,F (permuteRow π r)=fracPerm π (F r) := by
  let Good (π : Equiv.Perm (Fin 3)) : Prop := ∀ r,F (permuteRow π r)=fracPerm π (F r)
  have h1 : Good 1 := by
    intro r
    rw [fracPerm_one]
    rfl
  have hm {π σ : Equiv.Perm (Fin 3)} (hπ : Good π) (hσ : Good σ) : Good (π*σ) := by
    intro r
    rw [permuteRow_mul,hσ,hπ,fracPerm_mul]
  have hp {π : Equiv.Perm (Fin 3)} (hπ : Good π) (n : ℕ) : Good (π^n) := by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hm ih hπ
  have hswap : Good swapPerm := by
    intro r
    rw [permuteRow_swap,fracPerm_swap]
    exact hs r
  have hcycle : Good cyclePerm := by
    intro r
    rw [permuteRow_cycle,fracPerm_cycle]
    exact hc r
  intro π r
  obtain ⟨a,b,rfl⟩ := permutation_decomposition π
  exact hm (hp hcycle a.val) (hp hswap b.val) r

theorem flip_equivariance (F : Covector → Frac)
    (hp : ∀ π r,F (permuteRow π r)=fracPerm π (F r))
    (h3 : ∀ r,F (sign3 r)= -fracD3 (F r)) (i : Fin 3) (r : Covector) :
    F (flipRow i r)= -fracSign {i} (F r) := by
  rw [flipRow_conjugate,hp,h3,hp,map_neg,fracFlip_conjugate]

theorem sign_equivariance (F : Covector → Frac)
    (hf : ∀ i r,F (flipRow i r)= -fracSign {i} (F r)) :
    ∀ s r,F (signRow s r)=(-1 : ℚ)^s.card • fracSign s (F r) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro r
    rw [fracSign_empty]
    change F r=(1 : ℚ) • F r
    simp
  | @insert i s hi ih =>
    intro r
    rw [signRow_insert s i hi,hf,ih,
      map_rat_smul (fracSign {i}) ((-1 : ℚ)^s.card) (fracSign s (F r)),fracSign_insert s i hi,
      Finset.card_insert_of_notMem hi,pow_succ,mul_smul]
    rw [neg_one_smul ℚ (fracSign (insert i s) (F r))]
    exact (map_neg (((-1 : ℚ)^s.card) • (LinearMap.id : Frac →ₗ[ℚ] Frac))
      (fracSign (insert i s) (F r))).symm

/-- All six permutations of the literal rational seed table. -/
theorem seedValue_permutation {k : ℕ} (f : TP) (q : Fin k → BP)
    (hq : ∀ i, SymmetricBinaryPeriodRelations (q i)) (hc : C f=f) (hs : S f=f)
    (π : Equiv.Perm (Fin 3)) (r : Covector) :
    seedValue f q hq (permuteRow π r)=fracPerm π (seedValue f q hq r) :=
  permutation_equivariance _ (seedValue_swap f q hq hs) (seedValue_cycle f q hq hc hs) π r

/-- All48 signed permutations of the actual rational26-fiber system. -/
theorem seedValue_signed_permutation {k : ℕ} (f : TP) (q : Fin k → BP)
    (hq : ∀ i, SymmetricBinaryPeriodRelations (q i)) (hc : C f=f) (hs : S f=f)
    (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) (r : Covector) :
    seedValue f q hq (permuteRow π (signRow s r))=
      (-1 : ℚ)^s.card • fracPerm π (fracSign s (seedValue f q hq r)) := by
  rw [seedValue_permutation f q hq hc hs,
    sign_equivariance _ (flip_equivariance _ (seedValue_permutation f q hq hc hs)
      (seedValue_sign3 f q hq))]
  exact map_rat_smul (fracPerm π) ((-1 : ℚ)^s.card) (fracSign s (seedValue f q hq r))

end TernaryPoly.OrdinaryRationalFiber
