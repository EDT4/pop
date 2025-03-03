import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Pop.CategoryTheory.Limits.Shapes.SeqColimit
import Pop.NatExtras
import Pop.Util

section

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type _}
variable [Category C]
  -- TODO: Change these later
variable [HasPullbacks C]
variable [HasPushouts C]
variable [HasSeqColimits C]

-- TODO: Is this true?
instance instHasSeqColimitEndofunctor
  : [∀{s : Seq C}, HasSeqColimit s]
  → (∀{s : Seq (Functor C C)}, HasSeqColimit s)
  := sorry

-- TODO: Ideas for later
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Elements.html
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Sigma/Basic.html#CategoryTheory.Sigma.sigma
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/ObjectProperty/Basic.html
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/FullSubcategory.html#CategoryTheory.FullSubcategory
--   Why is FullSubcategory not using this type? https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Subtype
noncomputable def lem1 -- TODO: Should probably be computable when not using colim
  -- TODO: Reflective includes full and faithful, but it is already implied by F and G. Maybe not a problem?
  (A : ObjectProperty C) [Reflective (fullSubcategoryInclusion A)] [PreservesColimitsOfShape ℕ (fullSubcategoryInclusion A)]
  (B : ObjectProperty C) [Reflective (fullSubcategoryInclusion B)] [PreservesColimitsOfShape ℕ (fullSubcategoryInclusion B)]
  : Reflective (fullSubcategoryInclusion (❪ And ❫₂ A B))
  :=
    let TA : Functor C C := Adjunction.toMonad (reflectorAdjunction (fullSubcategoryInclusion A))
    let TB : Functor C C := Adjunction.toMonad (reflectorAdjunction (fullSubcategoryInclusion B))
    let Mseq := Seq.byIterate (TA ⋙ TB) sorry
    let Minf := seqColim Mseq
    -- TODO: When more stuff about seqcolim is proven. Something like TA ⋙ Minf = Minf ? Is it true?
    let inA : ∀(c : C), A (Minf.obj c) := sorry
    let inB : ∀(c : C), B (Minf.obj c) := sorry
    {
      L := FullSubcategory.lift (❪ And ❫₂ A B) Minf (fun c => .intro (inA c) (inB c))
      adj := sorry
    }

end
