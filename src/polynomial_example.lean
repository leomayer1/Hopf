import Hopf
import tactic

open_locale tensor_product
open_locale polynomial
open algebra.tensor_product
open polynomial

variables (K : Type) [comm_semiring K]

noncomputable def counit : K[X] →ₐ[K] K := polynomial.aeval 0

noncomputable def comul : K[X] →ₐ[K] K[X] ⊗[K] K[X] := polynomial.aeval ((polynomial.X ⊗ₜ 1) + (1 ⊗ₜ polynomial.X))

noncomputable def map1 : K[X] → K[X] ⊗ (K[X] ⊗ K[X]) := (map (alg_hom.id K K[X]) (comul K)) ∘ (comul K)

noncomputable def map2_1 : (K[X] ⊗[K] K[X] ⊗[K] K[X] → K[X] ⊗[K] (K[X] ⊗[K] K[X]) ) := (ring_theory.tensor_product.assoc K K[X] K[X] K[X])

noncomputable def map2_2 : (K[X] ⊗[K] K[X] →ₐ K[X] ⊗[K] K[X] ⊗[K] K[X] ) := map (comul K : K[X] →ₐ[K] K[X] ⊗[K] K[X]) (alg_hom.id K K[X])

noncomputable def map2_3 : K[X] →ₐ K[X] ⊗[K] K[X] := (comul K : K[X] →ₐ[K] K[X] ⊗[K] K[X])

noncomputable def map2 : (K[X] → K[X] ⊗[K] (K[X] ⊗[K] K[X]) ) := (map2_1 K) ∘ (map2_2 K) ∘ (map2_3 K)

lemma coassoc : map1 K = map2 K :=
begin
  have P : map1 K X = map2 K X,
  unfold map1,
  sorry,

end

