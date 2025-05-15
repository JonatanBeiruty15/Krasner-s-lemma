

import Mathlib

open IntermediateField

-- Define a p-norm on the algebraic closure of Q_p
variable (p : ℕ)[Fact (Nat.Prime p)]
noncomputable def PAdicNormExt (x : AlgebraicClosure ℚ_[p]) : ℝ :=
  let x' : adjoin ℚ_[p] ({x} : Set (AlgebraicClosure ℚ_[p])) := ⟨x, mem_adjoin_simple_self ℚ_[p] x⟩
  padicNormE ((Algebra.norm ℚ_[p] x')^(1/(Module.finrank ℚ_[p] (adjoin ℚ_[p] ({x} : Set (AlgebraicClosure ℚ_[p]))))))

--Jonatan
theorem non_arch (x y : AlgebraicClosure ℚ_[p]) : PAdicNormExt p (x + y) ≤
max (PAdicNormExt p x) (PAdicNormExt p y) := sorry



-- Characterization of conjugates via isomorphisms - Jonatan
-- For each a_i conjugate of a there is an isomorphisem σ of ℚ_p(a)--> ℚ_p(a_i) which keeps K = ℚ_p(b)
--       fixed and σ (a) = a_i








-- All extensions of ℚ_[p] are separable - Jonatan

open IntermediateField


theorem all_extensions_of_Q_p_separable
  (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] :
  Algebra.IsSeparable ℚ_[p] K :=
-- the characaristic of ℚ_p is 0 so every finite extension will be seperable
  by sorry
