import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Pop.CategoryTheory.OplaxPullback

namespace CategoryTheory.OplaxPullback

open CategoryTheory
open CategoryTheory.Limits

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable (L : A ⥤ C)
variable (R : B ⥤ C)

section
  variable (Rb : C ⥤ B)
  variable (Radj : Rb ⊣ R)

  @[simps!]
  def unprojLeft : A ⥤ OplaxPullback L R
    := OplaxPullback.liftL
      (𝟭 A)
      (L ⋙ Rb)
      (whiskerLeft L Radj.unit)
end

section
  variable (Lb : C ⥤ A)
  variable (Ladj : Lb ⊣ L)

  @[simps!]
  def unprojRight : B ⥤ OplaxPullback L R
    := OplaxPullback.liftR
      (R ⋙ Lb)
      (𝟭 B)
      (whiskerLeft R Ladj.unit)
end

namespace OfInitial
  variable [initb : HasInitial B]
  variable [initc : HasInitial C]

  @[simps!]
  noncomputable def unprojLeft : A ⥤ OplaxPullback L R where
    obj o := {
      left := o
      middle := initial C
      right := initial B
      homl := initial.to _
      homr := initial.to _
    }
    map f := {
      left   := f
      middle := 𝟙 _
      right  := 𝟙 _
    }
    -- := OplaxPullback.lift (𝟭 A) (initial (A ⥤ C)) (initial (A ⥤ B)) (initial.to _) (initial.to _)
    -- TODO: Probably possible to replace the definition by a lift. Then the unique morphism is not definitionally equal to above, but use uniqueness

  -- TODO: later
  -- @[simp] lemma unprojLeft_projLeft  : unprojLeft L R ⋙ projLeft  L R = 𝟭 A             := rfl
  -- @[simp] lemma unprojLeft_projMid   : unprojLeft L R ⋙ projMid   L R = initial (A ⥤ C) := rfl
  -- @[simp] lemma unprojLeft_projRight : unprojLeft L R ⋙ projRight L R = initial (A ⥤ B) := rfl

  noncomputable def projLeft_adj : unprojLeft L R ⊣ OplaxPullback.projLeft L R where
    unit := 𝟙 _
    counit := {app _ := {
      left   := 𝟙 _
      middle := initial.to _
      right  := initial.to _
    }}
end OfInitial

namespace OfInitial
  variable [inita : HasInitial A]
  variable [initc : HasInitial C]

  @[simps!]
  noncomputable def unprojRight : B ⥤ OplaxPullback L R where
    obj o := {
      left   := initial A
      middle := initial C
      right  := o
      homl := initial.to _
      homr := initial.to _
    }
    map f := {
      left   := 𝟙 _
      middle := 𝟙 _
      right  := f
    }
  -- := OplaxPullback.lift (initial (B ⥤ A)) (initial (B ⥤ C)) (𝟭 B) (initial.to _) (initial.to _)

  noncomputable def projRight_adj : unprojRight L R ⊣ OplaxPullback.projRight L R where
    unit := 𝟙 _
    counit := {app _ := {
      left   := initial.to _
      middle := initial.to _
      right  := 𝟙 _
    }}
end OfInitial
