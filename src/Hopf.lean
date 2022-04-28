import ring_theory.tensor_product

open_locale tensor_product
open algebra.tensor_product

variables (K : Type*) [comm_ring K]
variables (A : Type*) [comm_ring A] [algebra K A]

/- A big structure. There's a lot of uglinesshere...
  So much of the text here is making natural isomorphisms explicit...
  `tensor_product.assoc K A A A` is associativiy of tensor product,
  `map` is taking the tensor product of two algebra maps
  `alg_hom.id` is the identity, as an algebra map
  `tensor_product.lid` is saying that K is a left identity for K algebras under tensoring
  `algebra.of_id` is the structure morphism K →ₐ[K] A
  Should I add notation for these? Is there a way to have lean automatically do these?
-/
structure hopf_algebra :=
(comul : A →ₐ[K] A ⊗[K] A)
(counit : A →ₐ[K] K)
(coassoc : (tensor_product.assoc K A A A) ∘ (map comul (alg_hom.id K A)) ∘ comul = map (alg_hom.id K A) comul ∘ comul)
(counit_left : (tensor_product.lid K A) ∘ (map counit (alg_hom.id K A)) ∘ comul = (alg_hom.id K A))
(counit_right : (tensor_product.rid K A) ∘ (map (alg_hom.id K A) counit) ∘ comul = (alg_hom.id K A))
(coinv : A →ₐ[K] A)
(coinv_right : (lmul' K) ∘ (map (alg_hom.id K A) coinv) ∘ comul = (algebra.of_id K A) ∘ counit)
(coinv_left : (lmul' K) ∘ (map coinv (alg_hom.id K A)) ∘ comul = (algebra.of_id K A) ∘ counit)
.
