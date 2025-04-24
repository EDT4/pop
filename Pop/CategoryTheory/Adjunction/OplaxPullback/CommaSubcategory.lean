import Mathlib.CategoryTheory.Adjunction.Basic
import Pop.CategoryTheory.Adjunction.Comma
import Pop.CategoryTheory.Adjunction.OplaxPullback
import Pop.CategoryTheory.Adjunction.OplaxPullback.Comma
import Pop.CategoryTheory.CommaExtras
import Pop.CategoryTheory.OplaxPullback.Comma
import Pop.CategoryTheory.OplaxPullback.CommaSubcategory

namespace CategoryTheory.OplaxPullback

open CategoryTheory
open CategoryTheory.Limits

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable (L : A ⥤ C)
variable (R : B ⥤ C)
variable (Lb : C ⥤ A)
variable (Rb : C ⥤ B)
variable (Ladj : Lb ⊣ L)
variable (Radj : Rb ⊣ R)

namespace CommaLeft
  def unprojLeft : A ⥤ FullSubcategory (CommaLeft L R)
    := FullSubcategory.lift
      (CommaLeft L R)
      (OplaxPullback.unprojLeft L R Rb Radj)
      (fun a => IsIso.id (L.obj a))

  lemma unprojLeft_unfst_from_comma : unprojLeft L R Rb Radj = Comma.unfst L R Rb Radj ⋙ CommaLeft.from_comma := rfl
  lemma projLeft_to_comma_fst       : projLeft L R = OplaxPullback.CommaLeft.to_comma ⋙ Comma.fst _ _ := rfl

  variable [pua : HasPushouts A]
  variable [pub : HasPushouts B]

  noncomputable def unleft_left_adj : unprojLeft L R Rb Radj ⊣ CommaLeft.projLeft L R
    := Adjunction.comp (Comma.unfst_fst_adj _ _ _ _) OplaxPullback.CommaLeft.equiv_comma.symm.toAdjunction

  noncomputable def unincl : OplaxPullback L R ⥤ FullSubcategory (CommaLeft L R)
    := OplaxPullback.to_comma L R Rb Radj ⋙ OplaxPullback.CommaLeft.from_comma

  noncomputable def unincl_incl_adj : unincl L R Rb Radj ⊣ fullSubcategoryInclusion (CommaLeft L R)
    := Adjunction.ofNatIsoRight
      (Adjunction.comp
        (OplaxPullback.to_from_comma_adj L R Rb Radj)
        OplaxPullback.CommaLeft.equiv_comma.symm.toAdjunction
      )
      OplaxPullback.CommaLeft.to_from_inclusion

end CommaLeft

namespace CommaRight
  def unprojRight : B ⥤ FullSubcategory (CommaRight L R)
    := FullSubcategory.lift
      (CommaRight L R)
      (OplaxPullback.unprojRight L R Lb Ladj)
      (fun b => IsIso.id (R.obj b))

  lemma unprojRight_unfst_from_comma : unprojRight L R Lb Ladj = Comma.unfst R L Lb Ladj ⋙ CommaRight.from_comma := rfl
  lemma right_to_comma_fst : projRight L R = OplaxPullback.CommaRight.to_comma ⋙ Comma.fst _ _ := rfl

  variable [pua : HasPushouts A]
  variable [pub : HasPushouts B]

  noncomputable def unright_right_adj : unprojRight L R Lb Ladj ⊣ projRight L R
    := Adjunction.comp (Comma.unfst_fst_adj _ _ _ _) OplaxPullback.CommaRight.equiv_comma.symm.toAdjunction

  noncomputable def unincl : OplaxPullback L R ⥤ FullSubcategory (CommaRight L R)
    := OplaxPullback.flip ⋙ OplaxPullback.to_comma R L Lb Ladj ⋙ OplaxPullback.CommaRight.from_comma

  noncomputable def unincl_incl_adj : unincl L R Lb Ladj ⊣ fullSubcategoryInclusion (CommaRight L R)
    := Adjunction.ofNatIsoRight
      (
        let t := -- TODO: Does not work without a let? Is the reduction behaviour different?
          (Adjunction.comp
            (Adjunction.comp
              OplaxPullback.flipping.toAdjunction
              (OplaxPullback.to_from_comma_adj R L Lb Ladj)
            )
            OplaxPullback.CommaRight.equiv_comma.symm.toAdjunction
          )
        t
      )
      (OplaxPullback.CommaRight.to_from_inclusion)

end CommaRight
