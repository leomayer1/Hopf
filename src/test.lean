import ring_theory.tensor_product
import tactic

open_locale tensor_product
open_locale polynomial
open algebra.tensor_product

variables (K : Type) [comm_semiring K]

noncomputable def comul : K[X] →ₐ[K] K[X] ⊗[K] K[X] := polynomial.aeval ((polynomial.X ⊗ₜ 1) + (1 ⊗ₜ polynomial.X))

notation `Δ` :9000 := comul

noncomputable def map1 : K[X] → K[X] ⊗ (K[X] ⊗ K[X]) := (map (alg_hom.id K K[X]) (Δ K)) ∘ (Δ K : K[X] →ₐ[K] K[X] ⊗[K] K[X])

noncomputable def map2_1 : (K[X] ⊗[K] K[X] ⊗[K] K[X] → K[X] ⊗[K] (K[X] ⊗[K] K[X]) ) := (tensor_product.assoc K K[X] K[X] K[X])

noncomputable def map2_2 : (K[X] ⊗[K] K[X] → K[X] ⊗[K] K[X] ⊗[K] K[X] ) := map (Δ K : K[X] →ₐ[K] K[X] ⊗[K] K[X]) (alg_hom.id K K[X])

noncomputable def map2_3 : K[X] → K[X] ⊗[K] K[X] := (Δ K : K[X] →ₐ[K] K[X] ⊗[K] K[X])

noncomputable def map2 : (K[X] → K[X] ⊗[K] (K[X] ⊗[K] K[X]) ) := (map2_1 K) ∘ (map2_2 K) ∘ (map2_3 K)

lemma coassoc : map1 K = map2 K := -- this works
begin
  sorry,
end

lemma coassoc' : (map (alg_hom.id K K[X]) (Δ K)) ∘ (Δ K : K[X] →ₐ[K] K[X] ⊗[K] K[X]) = map2 K := -- this times out
begin
  sorry,
end


universes u v₁


variables {R : Type u} [comm_semiring R]
variables {A : Type v₁} [semiring A] [algebra R A]

variables (R A)

local attribute [elab_simple] alg_equiv_of_linear_equiv_triple_tensor_product
-- local attribute [elab_simple] assoc_aux_1
-- local attribute [elab_simple] assoc_aux_2

/-- The associator for tensor product of R-algebras, as an algebra isomorphism. -/
-- FIXME This is _really_ slow to compile. :-(
protected def assoc : ((A ⊗[R] A) ⊗[R] A) ≃ₐ[R] (A ⊗[R] (A ⊗[R] A)) :=
-- sorry
alg_equiv_of_linear_equiv_triple_tensor_product
  (tensor_product.assoc R A A A : (A ⊗ A ⊗ A) ≃ₗ[R] (A ⊗ (A ⊗ A))) (
    assoc_aux_1)
  (assoc_aux_2)
