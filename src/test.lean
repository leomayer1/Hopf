import ring_theory.tensor_product
import tactic

open_locale tensor_product
open_locale polynomial
open algebra.tensor_product
open polynomial

variables (K : Type) [comm_semiring K]

noncomputable def counit : K[X] →ₐ[K] K := polynomial.aeval 0

noncomputable def comul : K[X] →ₐ[K] K[X] ⊗[K] K[X] := polynomial.aeval ((polynomial.X ⊗ₜ 1) + (1 ⊗ₜ polynomial.X))


noncomputable def map1 : K[X] →ₐ K[X] ⊗ K[X] ⊗ K[X] := (algebra.tensor_product.assoc K K[X] K[X] K[X]).symm.to_alg_hom.comp ((map (alg_hom.id K K[X]) (comul K)).comp (comul K))

-- noncomputable def map2_1 : (K[X] ⊗[K] K[X] ⊗[K] K[X] →ₐ K[X] ⊗[K] (K[X] ⊗[K] K[X]) ) := (algebra.tensor_product.assoc K K[X] K[X] K[X]).to_alg_hom

-- noncomputable def map2_2 : (K[X] ⊗[K] K[X] →ₐ K[X] ⊗[K] K[X] ⊗[K] K[X] ) := map (comul K : K[X] →ₐ[K] K[X] ⊗[K] K[X]) (alg_hom.id K K[X])

-- noncomputable def map2_3 : K[X] →ₐ K[X] ⊗[K] K[X] := (comul K : K[X] →ₐ[K] K[X] ⊗[K] K[X])

noncomputable def map2 : (K[X] →ₐ K[X] ⊗[K] K[X] ⊗[K] K[X] ) :=  (map (comul K : K[X] →ₐ[K] K[X] ⊗[K] K[X]) (alg_hom.id K K[X])).comp (comul K : K[X] →ₐ[K] K[X] ⊗[K] K[X])

lemma coassoc : map1 K = map2 K :=
begin
  have P : map1 K X = map2 K X,
  unfold map1,
  unfold map2,
  unfold comul,
  rw aeval_X (X ⊗ₜ[K] 1 + 1 ⊗ₜ[K] X), -- why does this not work?
  unfold algebra.tensor_product.assoc,

  sorry,

end