-- https://leanprover-community.github.io/mathlib_docs/category_theory/functor/hom.html
-- THE PLAN IS TO DEFINE AN AFFINE GROUP SCHEME AS A REPRESENTABLE FUNCTOR FROM K-ALGEBRAS TO GROUPS, AND PROVE THAT G_a := Hom(K[X], _) IS AN AFFINE GROUP SCHEME

import category_theory.types
import algebra.category.Algebra.basic
import algebra.category.Group.basic
import data.polynomial.basic
import data.polynomial.algebra_map
import category_theory.over
import tactic

open_locale polynomial
open polynomial
open category_theory

variables (K : Type*) [comm_ring K]
-- variables (K_alg : Type*) [category K_alg] [category_theory.under K] -- category of commutative K-algebras. But how to use it...

class affine_scheme :=
(scheme : Algebra K ⥤ Type*)
(corepresentable : scheme.corepresentable)

class affine_group_scheme :=
(scheme : Algebra K ⥤ Group)
(corepresentable : (scheme ⋙ forget Group).corepresentable)

example : ∃ (f : coyoneda.obj (opposite.op (Algebra.of K K[X])) ⟶ forget (Algebra K)), is_iso f :=
begin

end

-- DEFINING G_a
instance G_a : affine_scheme K :=
{
  scheme := forget (Algebra K),
  corepresentable := begin
    refine {has_corepresentation := _},
    refine ⟨opposite.op (Algebra.of K K[X]), _⟩,
    -- need to contruct a natural tranformation Hom(K[X], _) ⟶ forget (Algebra K)
    -- see for an example of defining a natural transformation https://leanprover-community.github.io/mathlib_docs/category_theory/yoneda.html#category_theory.yoneda_lemma 
  end,
}

#check Algebra.of K K[X]
#check polynomial K

