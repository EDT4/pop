import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax

open CategoryTheory

universe u
variable {C : Type u} [Bicategory C]
variable {J : Type u} [Bicategory J]

-- TODO: Probably not correct. Check later
structure Cone (F : Pseudofunctor J C) where
  pt : C
  π : OplaxNatTrans ((const J).obj pt) F

-- TODO: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Bicategory/Basic.html https://mathoverflow.net/questions/137689/explicit-description-of-the-oplax-limit-of-a-functor-to-cat
-- TODO: What does comma have to do with this? Probably a special case in some way https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Comma/Basic.html#CategoryTheory.Comma
