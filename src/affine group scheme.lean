-- https://leanprover-community.github.io/mathlib_docs/category_theory/functor/hom.html
-- THE PLAN IS TO DEFINE AN AFFINE GROUP SCHEME AS A REPRESENTABLE FUNCTOR FROM K-ALGEBRAS TO GROUPS, AND PROVE THAT G_a := Hom(K[X], _) IS AN AFFINE GROUP SCHEME

-- TODO: want to only work with commutative algebras!

import category_theory.types
import algebra.category.Algebra.basic
import algebra.category.Group.basic
import data.polynomial.basic
import category_theory.over

open_locale polynomial
open polynomial
open category_theory

variables (K : Type*) [comm_ring K]
variables (K_alg : Type*) [category K_alg] [category_theory.under K] -- category of commutative K-algebras. But how to use it...

class affine_scheme :=
(scheme : Algebra K ⥤ Type*)
(corepresentable : scheme.corepresentable)

class affine_group_scheme :=
(scheme : Algebra K ⥤ Group)
(corepresentable : (scheme ⋙ forget Group).corepresentable)

-- DEFINING G_a
instance G_a : affine_scheme K :=
{
  scheme := forget (Algebra K),
  corepresentable := begin
    refine {has_corepresentation := _},
    sorry,
    -- use polynomial K, -- failed to instantiate goal with polynomial K
  end,
}