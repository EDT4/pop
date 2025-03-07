import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
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

lemma colimit_iso : (colimit f = colimit g)

noncomputable def lem1
  -- TODO: Reflective includes full and faithful, but it is already implied by F and G. Maybe not a problem?
  (A : ObjectProperty C)
  [Reflective (fullSubcategoryInclusion A)]
  (closed_a : ClosedUnderColimitsOfShape ℕ A)
  [ObjectProperty.IsClosedUnderIsomorphisms A]
  (B : ObjectProperty C)
  [Reflective (fullSubcategoryInclusion B)]
  (closed_b : ClosedUnderColimitsOfShape ℕ B)
  [ObjectProperty.IsClosedUnderIsomorphisms B]
  : Reflective (fullSubcategoryInclusion (❪ And ❫₂ A B))
  :=
    let TA : Monad C := (reflectorAdjunction (fullSubcategoryInclusion A)).toMonad
    let TB : Monad C := (reflectorAdjunction (fullSubcategoryInclusion B)).toMonad
    let M : Limits.Seq (C ⥤ C) := (Seq.iterate2 (c := Cat.of C) TA.toFunctor TB.toFunctor TA.η TB.η).step -- TODO: step should probably not be here, but on the subset
    let Minf : C ⥤ C := seqColim M -- TODO: Change later to computable
    let inA : ∀(c : C), A (Minf.obj c) := by -- TODO: inA and inB uses the same argument and should be generalised in the future
      intro c
      apply ObjectProperty.IsClosedUnderIsomorphisms.of_iso ((colimitIsoFlipCompColim M.diagram).app c).symm
      apply ClosedUnderColimitsOfShape.colimit closed_a (F := M.diagram.flip.obj c)
      intro n
      simp [M]
      -- TODO: Prove for order preserving injective map, iso?
      -- TODO: Do not use directly on Minf. Below is just an example of how it can be used
      apply Seq.Iterate2.odd_obj_property (c := Cat.of C) (mf := TA.η) (mg := TB.η) (fun _ (f : C ⥤ C) => (c : C) → A (f.obj c))
      . sorry -- simp [TA,reflector,fullSubcategoryInclusion,inducedFunctor,Reflective.L,FullSubcategory.obj] ; sorry
      . exact fun r c => r (TB.obj (TA.obj c))
      . sorry
    let inB : ∀(c : C), B (Minf.obj c) := by
      intro c
      apply ObjectProperty.IsClosedUnderIsomorphisms.of_iso ((colimitIsoFlipCompColim M.diagram).app c).symm
      apply ClosedUnderColimitsOfShape.colimit closed_b (F := M.diagram.flip.obj c)
      intro n
      simp [M]
      apply Seq.Iterate2.even_obj_property (c := Cat.of C) (mf := TA.η) (mg := TB.η) (fun {n} _ (f : Functor C C) => (n > 0) → (c : C) → B (f.obj c))
      . sorry -- simp [TA,reflector,fullSubcategoryInclusion,inducedFunctor,Reflective.L,FullSubcategory.obj] ; sorry
      . exact fun r o c => r sorry (TB.obj (TA.obj c))
      . sorry
      . sorry
    {
      L := FullSubcategory.lift (❪ And ❫₂ A B) Minf (fun c => .intro (inA c) (inB c))
      adj := sorry
    }

end
