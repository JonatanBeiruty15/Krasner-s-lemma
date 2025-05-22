import Mathlib

open IntermediateField Classical FiniteDimensional LinearMap LinearAlgebra

variable (p : ℕ)[Fact (Nat.Prime p)]
abbrev Q_p_bar := AlgebraicClosure ℚ_[p]

--Rank of field extension non-zero
lemma rank_neq_zero (K L : Type*)[Field K][Field L][Algebra K L][FiniteDimensional K L] : Module.finrank K L ≠ 0 :=
  Nat.pos_iff_ne_zero.1 Module.finrank_pos

--Reciprocal of rank is non-zero
lemma rec_rank_neq_zero (K L : Type*)[Field K][Field L][Algebra K L][FiniteDimensional K L] : 1/(Module.finrank K L : ℝ) ≠ 0 := by
  apply div_ne_zero
  exact Ne.symm (zero_ne_one' ℝ)
  exact Nat.cast_ne_zero.mpr (rank_neq_zero K L)

--Field-theoretic norm is multiplicative
theorem alg_norm_mul (K L : Type*)[Field K][Field L][Algebra K L][FiniteDimensional K L](x y : L) : (Algebra.norm K x)*(Algebra.norm K y) =
Algebra.norm K (x*y) := by
  dsimp[Algebra.norm]
  rw[← det_comp]
  have h : (mul K L) x ∘ₗ (mul K L) y = (mul K L) (x*y) := by
    ext z
    simp [mul_assoc]
  rw[h]

--Elements in a finite extension are algebraic
lemma finite_impl_alg {K M : Type*}[Field K][Field M][Algebra K M](L : IntermediateField K M)[FiniteDimensional K L]{x : M}(hx : x ∈ L) :
IsAlgebraic K x := by
  haveI : Module.Finite K L := inferInstance
  let y : L := ⟨x, hx⟩
  have hy : IsAlgebraic K y := IsAlgebraic.of_finite K y
  exact IsAlgebraic.algebraMap hy

--Extension by an algebraic element is finite
lemma simple_alg_ext_finite {K M : Type*}[Field K][Field M][Algebra K M]{x : M}(hx : IsAlgebraic K x) :
FiniteDimensional K (adjoin K ({x} : Set M)) := by
  have hint : IsIntegral K x := by exact IsAlgebraic.isIntegral hx
  exact adjoin.finiteDimensional hint

-- Extending norms
noncomputable def NormExt (K M : Type*)[NormedField K][Field M][Algebra K M](L : IntermediateField K M)(x : M)(hx : x ∈ L) : ℝ :=
  ‖Algebra.norm K (⟨x, hx⟩ : L)‖^(1/(Module.finrank K L : ℝ))

-- Extended norm is invariant of intermediate field
lemma NormExt_field_inv_help {K M : Type*}[NormedField K][Field M][Algebra K M](L : IntermediateField K M)
(hfinL : FiniteDimensional K L){x : M}(hLx : x ∈ L) : NormExt K M L x hLx = NormExt K M (adjoin K ({x} : Set M)) x
(mem_adjoin_simple_self K x) := by
  let Kx : IntermediateField K M := adjoin K ({x} : Set M)
  have Kx_le_L : Kx ≤ L := by exact adjoin_simple_le_iff.mpr hLx
  let inc : Kx →ₐ[K] L := inclusion Kx_le_L
  haveI : Algebra Kx L := (inc.toRingHom).toAlgebra
  haveI : IsScalarTower K Kx L := by
    have h : algebraMap K L = (algebraMap Kx L).comp (algebraMap K Kx) := by sorry
    exact IsScalarTower.of_algebraMap_eq' h
  unfold NormExt
  haveI : Module Kx L := Algebra.toModule
  have h1 : Module.finrank K L = (Module.finrank K Kx)*(Module.finrank Kx L) := by sorry
  have h2 : Algebra.norm K (⟨x, hLx⟩ : L) = (Algebra.norm K (⟨x, mem_adjoin_simple_self K x⟩ : Kx))^(Module.finrank Kx L) := by sorry
  rw[h2, norm_pow]
  have hnonneg : ‖Algebra.norm K (⟨x, mem_adjoin_simple_self K x⟩ : Kx)‖ ≥ 0 := by exact norm_nonneg ((Algebra.norm K) (⟨x, mem_adjoin_simple_self K x⟩ : Kx))
  rw[← Real.rpow_natCast_mul hnonneg]
  rw[h1]
  simp
  have h3 : (Module.finrank Kx L : ℝ)*((@Inv.inv ℝ DivInvMonoid.toInv (Module.finrank Kx L : ℝ)) * (@Inv.inv ℝ DivInvMonoid.toInv (Module.finrank K Kx : ℝ))) = 1/(Module.finrank K Kx : ℝ) := by sorry
  rw[h3]
  simp
  rfl


theorem NormExt_field_inv {K M : Type*}[NormedField K][Field M][Algebra K M](L N : IntermediateField K M)
(hfinL : FiniteDimensional K L)(hfinN : FiniteDimensional K N)
{x : M}(hLx : x ∈ L)(hNx : x ∈ N) : NormExt K M L x hLx = NormExt K M N x hNx := by
  let Kx : IntermediateField K M := adjoin K ({x} : Set M)
  have h1 : Kx ≤ L := by exact adjoin_simple_le_iff.mpr hLx
  have h2 : Kx ≤ N := by exact adjoin_simple_le_iff.mpr hNx
  have h3 : x ∈ Kx := by exact mem_adjoin_simple_self K x
  have halg : IsAlgebraic K x := finite_impl_alg L hLx
  have hfin : FiniteDimensional K Kx := by exact simple_alg_ext_finite halg
  have h4 : NormExt K M L x hLx = NormExt K M Kx x h3 := by rw[NormExt_field_inv_help L hfinL hLx]
  have h5 : NormExt K M N x hNx = NormExt K M Kx x h3 := by rw[NormExt_field_inv_help N hfinN hNx]
  rw[h4, h5]

--Extended norm is a norm
theorem zero_iff_NormExt_zero {K M : Type*}[NormedField K][Field M][Algebra K M](L : IntermediateField K M)[FiniteDimensional K L]{x : M}(hx : x ∈ L) :
x = 0 ↔ NormExt K M L x hx = 0 := by
  unfold NormExt
  rw [Real.rpow_eq_zero]
  rw[norm_eq_zero]
  rw[Algebra.norm_eq_zero_iff]
  exact beq_eq_beq.mp rfl
  exact norm_nonneg ((Algebra.norm K) (⟨x, hx⟩ : L))
  exact rec_rank_neq_zero K ↥L

theorem NormExt_mult {K M : Type*}[NormedField K][Field M][Algebra K M](L : IntermediateField K M)(h : FiniteDimensional K L){x y : M}(hx : x ∈ L)
(hy : y ∈ L)(hxy: x*y ∈ L) : NormExt K M L (x*y) hxy = (NormExt K M L x hx)*(NormExt K M L y hy) := by
  unfold NormExt
  have h1 : ‖Algebra.norm K (⟨x, hx⟩ : L)‖ ≥ 0 := by exact norm_nonneg ((Algebra.norm K) (⟨x, hx⟩ : L))
  have h2 : ‖Algebra.norm K (⟨y, hy⟩ : L)‖ ≥ 0 := by exact norm_nonneg ((Algebra.norm K) (⟨y, hy⟩ : L))
  have h3 : ‖Algebra.norm K (⟨x*y, hxy⟩ : L)‖ ≥ 0 := by exact norm_nonneg ((Algebra.norm K) (⟨x*y, hxy⟩ : L))
  have h4 : ‖Algebra.norm K (⟨x, hx⟩ : L)‖*‖Algebra.norm K (⟨y, hy⟩ : L)‖ ≥ 0 := by exact Left.mul_nonneg h1 h2
  rw[← Real.mul_rpow h1 h2]
  rw[Real.rpow_left_inj h3 h4 (rec_rank_neq_zero K L)]
  rw[← norm_mul]
  rw[alg_norm_mul K L ⟨x, hx⟩ ⟨y, hy⟩]
  rfl

lemma NormExt_neg_one {K M : Type*}[NormedField K][Field M][Algebra K M](L : IntermediateField K M)[FiniteDimensional K L](h : -1 ∈ L) : NormExt K M L (-1) h = 1 := by
  unfold NormExt
  refine (Real.eq_rpow_inv ?_ ?_ ?_).mp ?_
  exact norm_nonneg ((Algebra.norm K) (⟨-1, h⟩ : L))
  exact zero_le_one' ℝ
  exact rec_rank_neq_zero K L
  simp
  have h2 : (⟨-1, h⟩ : L) = -1 := by exact rfl
  have h3 : -1 = algebraMap K L (-1) := by simp
  rw[h2]
  have h1 : Algebra.norm K (-1 : L) = (-1)^(Module.finrank K L) := by
    rw[h3]
    exact Algebra.norm_algebraMap (-1)
  rw[h1]
  simp

--This is long and difficult
theorem NormExt_triangle {K M : Type*}[NormedField K][CompleteSpace K][Field M][Algebra K M](L : IntermediateField K M)[FiniteDimensional K L]{x y : M}(hx : x ∈ L)
(hy : y ∈ L)(hxy : x + y ∈ L) :
NormExt K M L (x + y) hxy ≤ NormExt K M L x hx + NormExt K M L y hy := sorry

--If the norm on K is non-Archimedian, then the extended norm is non-Archimedian, also long and difficult and maybe needs more assumptions
theorem NormExt_nonArch_if_nonArch {K M : Type*}[NormedField K][Field M][Algebra K M](L : IntermediateField K M)[FiniteDimensional K L]
{x y : M}(hx : x ∈ L)(hy : y ∈ L)(hxy : x + y ∈ L)(h : ∀ (a b : K), ‖a + b‖ ≤ max ‖a‖ ‖b‖) :
NormExt K M L (x + y) hxy ≤ max (NormExt K M L x hx) (NormExt K M L y hy) := sorry

--Norm is invariant under isomorphisms
theorem NormExt_iso_inv {K M : Type*}[NormedField K][Field M][Algebra K M](L N : IntermediateField K M)[FiniteDimensional K L]
[FiniteDimensional K N]{x : M}(hx : x ∈ L)(σ : L ≃ₐ[K] N)(hN : (σ (⟨x, hx⟩) : M) ∈ N) :
NormExt K M L x hx = NormExt K M N (σ ⟨x, hx⟩) hN := by
  unfold NormExt
  have h : Module.finrank K L = Module.finrank K N := by
    have e : L ≃ₗ[K] N := σ.toLinearEquiv
    exact LinearEquiv.finrank_eq e
  have h1: Module.finrank K ↑L = Module.finrank K ↑N := by exact h
  rw[h1]
  have h2 : ‖Algebra.norm K (⟨x, hx⟩ : L)‖ ≥ 0 := by exact norm_nonneg ((Algebra.norm K) (⟨x, hx⟩ : L))
  have h3 : ‖Algebra.norm K (σ ⟨x, hx⟩)‖ ≥ 0 := by exact norm_nonneg ((Algebra.norm K) (σ ⟨x, hx⟩))
  rw[Real.rpow_left_inj h2 h3 (rec_rank_neq_zero K N)]
  have hmain : Algebra.norm K (⟨x, hx⟩ : L) = Algebra.norm K (σ ⟨x, hx⟩) := by exact Eq.symm (Algebra.norm_eq_of_algEquiv σ ⟨x, hx⟩)
  exact congrArg norm hmain

-- Define a p-norm on the algebraic closure of `ℚ_[p]`
noncomputable def PAdicNormExt {p : ℕ}[Fact (Nat.Prime p)](x : Q_p_bar p) : ℝ :=
  NormExt ℚ_[p] (Q_p_bar p) (adjoin ℚ_[p] ({x} : Set (Q_p_bar p))) x (mem_adjoin_simple_self ℚ_[p] x)

theorem PAdicNormExt_non_arch {p : ℕ}[Fact (Nat.Prime p)](x y : AlgebraicClosure ℚ_[p]) : PAdicNormExt (x + y) ≤
max (PAdicNormExt x) (PAdicNormExt y) := by
  let Kx : IntermediateField ℚ_[p] (Q_p_bar p) := adjoin ℚ_[p] ({x} : Set (Q_p_bar p))
  let Ky : IntermediateField ℚ_[p] (Q_p_bar p) := adjoin ℚ_[p] ({y} : Set (Q_p_bar p))
  let Kxy : IntermediateField ℚ_[p] (Q_p_bar p) := adjoin ℚ_[p] ({x, y} : Set (Q_p_bar p))
  let Kxpy : IntermediateField ℚ_[p] (Q_p_bar p) := adjoin ℚ_[p] ({x + y} : Set (Q_p_bar p))
  let S : Set (Q_p_bar p) := {x, y}
  unfold PAdicNormExt
  have h : ∀ (a b : ℚ_[p]), ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by exact fun a b ↦ padicNormE.nonarchimedean a b
  have hx : x ∈ Kxy := by exact mem_adjoin_pair_left ℚ_[p] x y
  have hx1 : x ∈ Kx := by exact mem_adjoin_simple_self ℚ_[p] x
  have hy : y ∈ Kxy := by exact mem_adjoin_pair_right ℚ_[p] x y
  have hy1 : y ∈ Ky := by exact mem_adjoin_simple_self ℚ_[p] y
  have hz : x + y ∈ Kxy := by exact IntermediateField.add_mem Kxy hx hy
  have hz1 : x + y ∈ Kxpy := by exact mem_adjoin_simple_self ℚ_[p] (x + y)
  have hS : ∀ z ∈ S, IsIntegral ℚ_[p] z := by
    intro z hz
    have help: IsAlgebraic ℚ_[p] z := Algebra.IsAlgebraic.isAlgebraic z
    exact IsAlgebraic.isIntegral help
  have hfin : FiniteDimensional ℚ_[p] Kxy := by exact finiteDimensional_adjoin hS
  have hfinx : FiniteDimensional ℚ_[p] Kx := by
    have hx2 : IsAlgebraic ℚ_[p] x := Algebra.IsAlgebraic.isAlgebraic x
    exact simple_alg_ext_finite hx2
  have hfiny : FiniteDimensional ℚ_[p] Ky := by
    have hy2 : IsAlgebraic ℚ_[p] y := Algebra.IsAlgebraic.isAlgebraic y
    exact simple_alg_ext_finite hy2
  have hfins : FiniteDimensional ℚ_[p] Kxpy := by
    have hxpy2 : IsAlgebraic ℚ_[p] (x + y) := Algebra.IsAlgebraic.isAlgebraic (x + y)
    exact simple_alg_ext_finite hxpy2
  rw[← NormExt_field_inv Kxy Kx hfin hfinx hx hx1]
  rw[← NormExt_field_inv Kxy Ky hfin hfiny hy hy1]
  rw[← NormExt_field_inv Kxy Kxpy hfin hfins hz hz1]
  exact NormExt_nonArch_if_nonArch Kxy hx hy hz h

theorem PAdicNormExt_mult_minus {p : ℕ}[Fact (Nat.Prime p)](x : AlgebraicClosure ℚ_[p]) : PAdicNormExt x = PAdicNormExt (-x) := by
  let K1 : IntermediateField ℚ_[p] (Q_p_bar p) := adjoin ℚ_[p] ({x} : Set (Q_p_bar p))
  let K3 : IntermediateField ℚ_[p] (Q_p_bar p) := adjoin ℚ_[p] ({-1*x} : Set (Q_p_bar p))
  unfold PAdicNormExt
  have hx' : IsAlgebraic ℚ_[p] x := Algebra.IsAlgebraic.isAlgebraic x
  have hfin1 : FiniteDimensional ℚ_[p] K1 := simple_alg_ext_finite hx'
  rw[← neg_one_mul]
  have h1' : 1 ∈ K3 := by exact IntermediateField.one_mem K3
  have h1 : (-1) ∈ K3 := by exact IntermediateField.neg_mem K3 h1'
  have h3 : -1*x ∈ K3 := by exact mem_adjoin_simple_self ℚ_[p] (-1 * x)
  have h2' : -x ∈ K3 := by
    rw[← neg_one_mul]
    exact h3
  have h2 : x ∈ K3 := by exact neg_mem_iff.mp h2'
  have halg : IsAlgebraic ℚ_[p] (-1*x) := Algebra.IsAlgebraic.isAlgebraic (-1*x)
  have hfin3 : FiniteDimensional ℚ_[p] K3 := by exact simple_alg_ext_finite halg
  rw[NormExt_mult K3 hfin3 h1 h2 h3]
  rw[NormExt_neg_one K3 h1, one_mul]
  exact NormExt_field_inv ℚ_[p]⟮x⟯ K3 hfin1 hfin3 (PAdicNormExt._proof_2 x) h2

theorem PAdicNormExt_iso_inv {p : ℕ}[Fact (Nat.Prime p)](L N : IntermediateField ℚ_[p] (Q_p_bar p))[FiniteDimensional ℚ_[p] L]
[FiniteDimensional ℚ_[p] N]{x : Q_p_bar p}(hx : x ∈ L)(σ : L ≃ₐ[ℚ_[p]] N)(hN : (σ (⟨x, hx⟩) : Q_p_bar p) ∈ N) :
PAdicNormExt x = PAdicNormExt (σ (⟨x, hx⟩) : Q_p_bar p) := by
  unfold PAdicNormExt
  let Kx : IntermediateField ℚ_[p] (Q_p_bar p) := adjoin ℚ_[p] ({x} : Set (Q_p_bar p))
  have hx1 : x ∈ Kx := by exact mem_adjoin_simple_self ℚ_[p] x
  have hxalg : IsAlgebraic ℚ_[p] x := by exact finite_impl_alg L hx
  have hfinL : FiniteDimensional ℚ_[p] L := by (expose_names; exact inst_1)
  have hfinx : FiniteDimensional ℚ_[p] Kx := by exact simple_alg_ext_finite hxalg
  rw[← NormExt_field_inv L Kx hfinL hfinx hx hx1]
  let K : IntermediateField ℚ_[p] (Q_p_bar p) := adjoin ℚ_[p] ({(σ (⟨x, hx⟩) : Q_p_bar p)} : Set (Q_p_bar p))
  have h1 : (σ (⟨x, hx⟩) : Q_p_bar p) ∈ K := by exact mem_adjoin_simple_self ℚ_[p] (σ (⟨x, hx⟩) : Q_p_bar p)
  have h1alg : IsAlgebraic ℚ_[p] (σ (⟨x, hx⟩) : Q_p_bar p) := by exact finite_impl_alg N hN
  have hfinN : FiniteDimensional ℚ_[p] N := by (expose_names; exact inst_2)
  have hfin1 : FiniteDimensional ℚ_[p] K := by exact simple_alg_ext_finite h1alg
  rw[← NormExt_field_inv N K hfinN hfin1 hN h1]
  exact NormExt_iso_inv L N hx σ hN

theorem PAdicNormExt_big_iso_inv {p : ℕ}[Fact (Nat.Prime p)](K : IntermediateField ℚ_[p] (Q_p_bar p))(x : Q_p_bar p)
(σ : (Q_p_bar p) ≃ₐ[ℚ_[p]] (Q_p_bar p)) : PAdicNormExt x = PAdicNormExt (σ x) := by
  let Kx : IntermediateField ℚ_[p] (Q_p_bar p) := adjoin ℚ_[p] ({x} : Set (Q_p_bar p))
  let Ksx : IntermediateField ℚ_[p] (Q_p_bar p) := adjoin ℚ_[p] ({σ x} : Set (Q_p_bar p))
  sorry

-- Characterization of conjugates via isomorphisms
theorem exists_isomorphism_to_conjugate (K : Type*)[Field K](a b: AlgebraicClosure K)(h: IsConjRoot K a b):
let Ka := IntermediateField.adjoin K {a}
let Kb := IntermediateField.adjoin K {b}
∃ (σ : Ka ≃ₐ[K] Kb), σ ⟨a, mem_adjoin_simple_self K a⟩ = ⟨b, mem_adjoin_simple_self K b⟩:= by sorry

-- All extensions of `ℚ_[p]` are separable
theorem all_extensions_of_Q_p_separable {p : ℕ}[Fact (Nat.Prime p)](K : Type*)[Field K][Algebra ℚ_[p] K][FiniteDimensional ℚ_[p] K] :
Algebra.IsSeparable ℚ_[p] K := sorry

--Main part of the proof of Krasner's lemma
lemma lemma_main {p : ℕ}[Fact (Nat.Prime p)](a b : AlgebraicClosure ℚ_[p])
(h : ∀ (x : AlgebraicClosure ℚ_[p]), x ≠ a ∧ IsConjRoot ℚ_[p] a x → PAdicNormExt (b - a) < PAdicNormExt (x - a)) :
a ∈ adjoin ℚ_[p] ({b} : Set (AlgebraicClosure ℚ_[p])) := by
  by_contra h1
  let K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]) := adjoin ℚ_[p] ({b} : Set (AlgebraicClosure ℚ_[p]))
  let L : IntermediateField K (AlgebraicClosure ℚ_[p]) := adjoin K ({a} : Set (AlgebraicClosure ℚ_[p]))
  -- For the proof of h2, use not_mem_iff_exists_ne_and_isConjRoot (with K and AlgebraicClosure ℚ_[p])
  -- Ingredients needed: a separable over K and minimal polynomial of a over K splits over AlgebraicClosure ℚ_[p]
  have h2 : ∃ (c : AlgebraicClosure ℚ_[p]), a ≠ c ∧ IsConjRoot K a c := by sorry
  sorry

/-- If `a ∈ K(b)`, then the intermediate field `K(a)` is contained in `K(b)`. -/
theorem adjoin_of_mem_adjoin {K : Type*} [Field K] (a b : AlgebraicClosure K)
  (h : a ∈ adjoin K ({b} : Set (AlgebraicClosure K))) :
  adjoin K ({a} : Set (AlgebraicClosure K)) ≤ adjoin K ({b} : Set (AlgebraicClosure K)) :=
  adjoin_le_iff.2 (Set.singleton_subset_iff.2 h)

theorem lemma_krasner {p : ℕ}[Fact (Nat.Prime p)](a b : AlgebraicClosure ℚ_[p])
(h : ∀ (x : AlgebraicClosure ℚ_[p]), x ≠ a ∧ IsConjRoot ℚ_[p] a x → PAdicNormExt (b - a) < PAdicNormExt (x - a)) :
adjoin ℚ_[p] ({a} : Set (AlgebraicClosure ℚ_[p])) ≤ adjoin ℚ_[p] ({b} : Set (AlgebraicClosure ℚ_[p])) :=
  have ha : a ∈ adjoin ℚ_[p] ({b} : Set (AlgebraicClosure ℚ_[p])) := lemma_main a b h
  adjoin_of_mem_adjoin a b ha
