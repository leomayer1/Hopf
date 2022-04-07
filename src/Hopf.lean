import ring_theory.tensor_product
import algebra.monoid_algebra.basic
import data.polynomial.algebra_map

open_locale tensor_product

open algebra.tensor_product

variables (K : Type) [field K]
variables (V : Type) [semiring V] [algebra K V]



/- A coalgebra class, i.e a vector space with maps which look like the algebra maps,
  but with arrows flipped.
  Maybe it would be nicer to make classes for has_comul, has_counit, has_coassoc, etc.
-/

class hopf_algebra extends algebra K V :=
(comul : V →ₐ[K] V ⊗ V)
(counit : V →ₐ[K] K)
(coassoc : (tensor_product.assoc K V V V) ∘ (map comul (alg_hom.id K V)) ∘ comul = map (alg_hom.id K V) comul ∘ comul)
(counit_left : (tensor_product.lid K V) ∘ (map counit (alg_hom.id K V)) ∘ comul = (alg_hom.id K V))
(counit_right : (tensor_product.rid K V) ∘ (map (alg_hom.id K V) counit) ∘ comul = (alg_hom.id K V))
(coinv : V →ₗ[K] V)
--(coinv_right : mul ∘ (map id coinv) ∘ comul = unit ∘ counit)
--(coinv_left : mul ∘ (map coinv id) ∘ comul = unit ∘ counit)

/- Group ring of an abelian group is actually a hopf algebra? -/

notation K`[x]`:9000 := polynomial K

--def comul : K[x] →ₗ[K] K[x] ⊗ K[x] := sorry
