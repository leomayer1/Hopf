import Hopf
import tactic

open_locale tensor_product
open_locale polynomial
open algebra.tensor_product

variables (K : Type) [field K]

noncomputable def counit : K[X] →ₐ[K] K := polynomial.aeval 0

noncomputable def comul : K[X] →ₐ[K] K[X] ⊗[K] K[X] := polynomial.aeval ((polynomial.X ⊗ₜ 1) + (1 ⊗ₜ polynomial.X))

notation `Δ` :9000 := comul

noncomputable def map1 : (K[X] → K[X] ⊗[K] (K[X] ⊗[K] K[X]) ) := (map (alg_hom.id K K[X]) (Δ K)) ∘ (Δ K)

noncomputable def map2_1 : (K[X] ⊗[K] K[X] ⊗[K] K[X] → K[X] ⊗[K] (K[X] ⊗[K] K[X]) ) := (tensor_product.assoc K K[X] K[X] K[X])

#check (Δ K)
#check map (alg_hom.id K K[X])
-- Stuff below breaks :(
#check map (Δ K)

noncomputable def map2_2 : (K[X] ⊗[K] K[X] → K[X] ⊗[K] K[X] ⊗[K] K[X] ) := map (Δ K) (alg_hom.id K K[X])

noncomputable def map2_3 : (K[X] → K[X] ⊗[K] K[X]) := Δ K

noncomputable def map2 : (K[X] → K[X] ⊗[K] (K[X] ⊗[K] K[X]) ) := (tensor_product.assoc K K[X] K[X] K[X]) ∘ (map (Δ K) (alg_hom.id K K[X])) ∘ (Δ K)

noncomputable lemma coassoc : map1 = map2 :=
begin
  sorry,
end

