import ring_theory.tensor_product

open_locale tensor_product
open algebra.tensor_product

variables (K : Type) [field K]
variables (V : Type) [comm_ring V] [algebra K V]

/- A big structure. There's a lot of uglinesshere...
  So much of the text here is making natural isomorphisms explicit...
  `tensor_product.assoc K V V V` is associativiy of tensor product,
  `map` is taking the tensor product of two algebra maps
  `alg_hom.id` is the identity, as an algebra map
  `tensor_product.lid` is saying that K is a left identity for K algebras under tensoring
  `algebra.of_id` is the structure morphism K →ₐ[K] V
  Should I add notation for these? Is there a way to have lean automatically do these?
-/
structure hopf_algebra :=
(comul : V →ₐ[K] V ⊗[K] V)
(counit : V →ₐ[K] K)
(coassoc : (tensor_product.assoc K V V V) ∘ (map comul (alg_hom.id K V)) ∘ comul = map (alg_hom.id K V) comul ∘ comul)
(counit_left : (tensor_product.lid K V) ∘ (map counit (alg_hom.id K V)) ∘ comul = (alg_hom.id K V))
(counit_right : (tensor_product.rid K V) ∘ (map (alg_hom.id K V) counit) ∘ comul = (alg_hom.id K V))
(coinv : V →ₐ[K] V)
(coinv_right : (lmul' K) ∘ (map (alg_hom.id K V) coinv) ∘ comul = (algebra.of_id K V) ∘ counit)
(coinv_left : (lmul' K) ∘ (map coinv (alg_hom.id K V)) ∘ comul = (algebra.of_id K V) ∘ counit)

notation K`[X]`:9000 := polynomial K

noncomputable def comul : K[X] →ₐ[K] K[X] ⊗[K] K[X] := polynomial.aeval ((polynomial.X ⊗ₜ 1) + (1 ⊗ₜ polynomial.X))

notation `Δ` :9000 := comul

noncomputable def counit : K[X] →ₐ[K] K := polynomial.aeval 0

noncomputable def map1 : (K[X] → K[X] ⊗[K] (K[X] ⊗[K] K[X]) ) := (map (alg_hom.id K K[X]) (Δ K)) ∘ (Δ K)

noncomputable def map2_1 : (K[X] ⊗[K] K[X] ⊗[K] K[X] → K[X] ⊗[K] (K[X] ⊗[K] K[X]) ) := (tensor_product.assoc K K[X] K[X] K[X])

#check (Δ K)
#check map (alg_hom.id K K[X]) (alg_hom.id K K[X])
-- Stuff below breaks :(
#check map (Δ K)

noncomputable def map2_2 : (K[X] ⊗[K] K[X] → K[X] ⊗[K] K[X] ⊗[K] K[X] ) := map (Δ K) (alg_hom.id K K[X])

noncomputable def map2_3 : (K[X] → K[X] ⊗[K] K[X]) := Δ K

noncomputable def map2 : (K[X] → K[X] ⊗[K] (K[X] ⊗[K] K[X]) ) := (tensor_product.assoc K K[X] K[X] K[X]) ∘ (map (Δ K) (alg_hom.id K K[X])) ∘ (Δ K)

noncomputable lemma coassoc : map1 = map2 :=
begin
  sorry,
end
