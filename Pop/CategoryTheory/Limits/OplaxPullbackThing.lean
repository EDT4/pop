import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Pop.CategoryTheory.OplaxPullbackThing

namespace CategoryTheory.OplaxPullbackThing

open CategoryTheory.Limits

universe s s'
variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable {J : Type _} [Category J]
variable {L : A ⥤ C}
variable {R : B ⥤ C}
variable (F : J ⥤ OplaxPullbackThing L R)

-- instance hasLimit
--   (F : J ⥤ OplaxPullbackThing L R)
--   [HasLimit (F ⋙ leftFunctor   L R)]
--   [HasLimit (F ⋙ middleFunctor L R)]
--   [HasLimit (F ⋙ rightFunctor  L R)]
--   [PreservesLimit (F ⋙ rightFunctor L R) R]
--   : HasLimit F
--   := sorry
--
-- instance hasLimitsOfShape
--   [HasLimitsOfShape J A]
--   [HasLimitsOfShape J B]
--   [PreservesLimitsOfShape J L]
--   : HasLimitsOfShape J (OplaxPullbackThing L R)
--   where
--
-- instance hasLimitsOfSize
--   [HasLimitsOfSize.{s,s'} A]
--   [HasLimitsOfSize.{s,s'} B]
--   [PreservesLimitsOfSize.{s,s'} R]
--   : HasLimitsOfSize.{s,s'} (OplaxPullbackThing L R)
--   := fun _ _ => inferInstance

@[simps!]
def coconePrecompose_llm
  (c : Cocone (F ⋙ leftFunctor L R))
  : Cocone (F ⋙ middleFunctor L R)
  := (Cocones.precompose (whiskerLeft F (OplaxPullbackThing.llm L R))).obj (L.mapCocone c)

@[simps!]
def coconePrecompose_rrm
  (c : Cocone (F ⋙ rightFunctor L R))
  : Cocone (F ⋙ middleFunctor L R)
  := (Cocones.precompose (whiskerLeft F (OplaxPullbackThing.rrm L R))).obj (R.mapCocone c)

instance hasColimit
  [hl : HasColimit (F ⋙ leftFunctor   L R)]
  [hm : HasColimit (F ⋙ middleFunctor L R)]
  [hr : HasColimit (F ⋙ rightFunctor  L R)]
  [pl : PreservesColimit (F ⋙ leftFunctor L R) L]
  : HasColimit F
  := HasColimit.mk ⟨sorry,sorry⟩

instance hasColimitsOfShape
  [ha : HasColimitsOfShape J A]
  [hb : HasColimitsOfShape J B]
  [hc : HasColimitsOfShape J C]
  [pl : PreservesColimitsOfShape J L]
  : HasColimitsOfShape J (OplaxPullbackThing L R)
  where

instance hasColimitsOfSize
  [ha : HasColimitsOfSize.{s,s'} A]
  [hb : HasColimitsOfSize.{s,s'} B]
  [hc : HasColimitsOfSize.{s,s'} C]
  [pl : PreservesColimitsOfSize.{s,s'} L]
  : HasColimitsOfSize.{s,s'} (OplaxPullbackThing L R)
  := ⟨fun _ _ => inferInstance⟩
