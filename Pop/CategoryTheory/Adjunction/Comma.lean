import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Pop.CategoryTheory.Adjunction.MkExtras
import Pop.CategoryTheory.CommaExtras

namespace CategoryTheory.Comma

open CategoryTheory

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable (L : A ⥤ C)
variable (R : B ⥤ C)

section
  variable (Rb : C ⥤ B)
  variable (Radj : Rb ⊣ R)

  @[simps!]
  def unfst : A ⥤ Comma L R
    := Comma.lift
      (𝟭 A)
      (L ⋙ Rb)
      (whiskerLeft L Radj.unit)

  @[simp] lemma unfst_fst : unfst L R Rb Radj ⋙ fst L R = 𝟭 A     := rfl
  @[simp] lemma unfst_snd : unfst L R Rb Radj ⋙ snd L R = L ⋙ Rb := rfl

  def unfst_fst_adj : Comma.unfst L R Rb Radj ⊣ Comma.fst L R where
    unit := 𝟙 (𝟭 A)
    counit := Comma.liftTrans
      (𝟙 _)
      (((Adjunction.homEquiv (Adjunction.whiskerRight _ Radj)) (fst L R ⋙ L) (snd L R)).invFun (Comma.natTrans L R))
      (by ext ; simp [Adjunction.homEquiv])
    left_triangle_components _ := by ext <;> simp [Adjunction.homEquiv]
end

section
  variable (Lb : C ⥤ A)
  variable (Ladj : L ⊣ Lb)

  @[simps!]
  def unsnd : B ⥤ Comma L R
    := Comma.lift
      (R ⋙ Lb)
      (𝟭 B)
      (whiskerLeft R Ladj.counit)

  @[simp] lemma unsnd_fst : unsnd L R Lb Ladj ⋙ fst L R = R ⋙ Lb := rfl
  @[simp] lemma unsnd_snd : unsnd L R Lb Ladj ⋙ snd L R = 𝟭 B     := rfl

  def unsnd_snd_adj : Comma.snd L R ⊣ Comma.unsnd L R Lb Ladj where
    counit := 𝟙 (𝟭 B)
    unit := Comma.liftTrans
      (((Adjunction.homEquiv (Adjunction.whiskerRight _ Ladj)) (fst L R) (snd L R ⋙ R)).toFun (Comma.natTrans L R))
      (𝟙 _)
      (by ext ; simp [Adjunction.homEquiv])
    right_triangle_components _ := by ext <;> simp [Adjunction.homEquiv]

end
