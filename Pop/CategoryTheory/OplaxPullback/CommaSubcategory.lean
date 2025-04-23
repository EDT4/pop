import Mathlib.CategoryTheory.Comma.Basic
import Pop.CategoryTheory.CommaExtras
import Pop.CategoryTheory.FullSubcategoryExtras
import Pop.CategoryTheory.OplaxPullback
import Pop.CategoryTheory.OplaxPullback.Comma

namespace CategoryTheory.OplaxPullback

open CategoryTheory

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable {D : Type _} [Category D]
variable (L : A ⥤ C)
variable (R : B ⥤ C)

-- Partially-oplax pullback (on the left).
-- `OplaxPullback`s where `homl` is an isomorphism.
def CommaLeft : Set (OplaxPullback L R) := fun p => IsIso p.homl

namespace CommaLeft
  abbrev projLeft : FullSubcategory (CommaLeft L R) ⥤ A
    := fullSubcategoryInclusion _ ⋙ OplaxPullback.projLeft _ _

  abbrev projMid : FullSubcategory (CommaLeft L R) ⥤ C
    := fullSubcategoryInclusion _ ⋙ OplaxPullback.projMid _ _

  abbrev projRight : FullSubcategory (CommaLeft L R) ⥤ B
    := fullSubcategoryInclusion _ ⋙ OplaxPullback.projRight _ _

  abbrev llm : projMid L R ⟶ projLeft L R ⋙ L
    := whiskerLeft _ (OplaxPullback.llm _ _)

  abbrev rrm : projMid L R ⟶ projRight L R ⋙ R
    := whiskerLeft _ (OplaxPullback.rrm _ _)

  noncomputable def mll : projLeft L R ⋙ L ⟶ projMid L R where
    app o := inv _ (I := o.property)

  noncomputable def llem : projMid L R ≅ projLeft L R ⋙ L where
    hom := llm _ _
    inv := mll _ _
    hom_inv_id := by unfold llm ; unfold mll ; aesop
    inv_hom_id := by unfold llm ; unfold mll ; aesop

  noncomputable abbrev natTrans : projLeft L R ⋙ L ⟶ projRight L R ⋙ R
    := mll _ _ ≫ rrm _ _

  variable {L R}

  def from_comma : Comma L R ⥤ FullSubcategory (CommaLeft L R)
    := FullSubcategory.lift
      (CommaLeft L R)
      (OplaxPullback.from_comma L R)
      (by simp [OplaxPullback.from_comma,CommaLeft] ; infer_instance)

  @[simp] lemma from_comma_projLeft  : from_comma ⋙ projLeft  L R = Comma.fst L R := rfl
  @[simp] lemma from_comma_projRight : from_comma ⋙ projRight L R = Comma.snd L R := rfl
  @[simp] lemma from_comma_inclusion : from_comma ⋙ fullSubcategoryInclusion (CommaLeft L R) = OplaxPullback.from_comma L R := rfl

  noncomputable def to_comma : FullSubcategory (CommaLeft L R) ⥤ Comma L R
    := Comma.lift (projLeft _ _) (projRight _ _) (natTrans _ _)

  @[simp] lemma to_comma_fst : to_comma ⋙ Comma.fst L R = projLeft  L R := Comma.lift_fst
  @[simp] lemma to_comma_snd : to_comma ⋙ Comma.snd L R = projRight L R := Comma.lift_snd

  noncomputable def from_to_inverse : from_comma ⋙ to_comma ≅ 𝟭 (Comma L R)
    := Comma.liftIso
      (Iso.refl _)
      (Iso.refl _)
      (by ext ; simp [to_comma,from_comma,mll])
      (by ext ; simp [to_comma,from_comma,mll])

  noncomputable def to_from_inverse : to_comma ⋙ from_comma ≅ 𝟭 (FullSubcategory (CommaLeft L R))
    := FullSubcategory.liftIso _ $ OplaxPullback.liftIso
      (Iso.refl _)
      (llem _ _).symm
      (Iso.refl _)
      (by ext ; simp [to_comma,from_comma,llem,mll])
      (by ext ; simp [to_comma,from_comma,llem,mll])
      (by ext ; simp [to_comma,from_comma,llem,mll])
      (by ext ; simp [to_comma,from_comma,llem,mll])

  noncomputable def to_from_inclusion : to_comma ⋙ OplaxPullback.from_comma L R ≅ fullSubcategoryInclusion (CommaLeft L R)
    := isoWhiskerRight to_from_inverse (fullSubcategoryInclusion (CommaLeft L R))

  noncomputable def equiv_comma : FullSubcategory (CommaLeft L R) ≌ Comma L R
    := Equivalence.mk
      to_comma
      from_comma
      to_from_inverse.symm
      from_to_inverse

end CommaLeft

-- Partially-oplax pullback (on the right).
-- `OplaxPullback`s where `homr` is an isomorphism.
def CommaRight : Set (OplaxPullback L R) := CommaLeft R L ∘ flip.obj

def comma_left_right : FullSubcategory (CommaLeft L R) ≌ FullSubcategory (CommaRight R L)
  := Equivalence.mk
    (FullSubcategory.lift _ (fullSubcategoryInclusion _ ⋙ flip) FullSubcategory.property)
    (FullSubcategory.lift _ (fullSubcategoryInclusion _ ⋙ flip) FullSubcategory.property)
    (NatIso.ofComponents (fun _ => Iso.refl _))
    (NatIso.ofComponents (fun _ => Iso.refl _))

def comma_left_right_inclusion_flip : (comma_left_right L R).functor ⋙ fullSubcategoryInclusion (CommaRight R L) = fullSubcategoryInclusion (CommaLeft  L R) ⋙ OplaxPullback.flip := rfl
def comma_right_left_inclusion_flip : (comma_left_right L R).inverse ⋙ fullSubcategoryInclusion (CommaLeft  L R) = fullSubcategoryInclusion (CommaRight R L) ⋙ OplaxPullback.flip := rfl

namespace CommaRight
  abbrev projLeft : FullSubcategory (CommaRight L R) ⥤ A
    := fullSubcategoryInclusion _ ⋙ OplaxPullback.projLeft _ _

  abbrev projMid : FullSubcategory (CommaRight L R) ⥤ C
    := fullSubcategoryInclusion _ ⋙ OplaxPullback.projMid _ _

  abbrev projRight : FullSubcategory (CommaRight L R) ⥤ B
    := fullSubcategoryInclusion _ ⋙ OplaxPullback.projRight _ _

  abbrev llm : projMid L R ⟶ projLeft L R ⋙ L
    := whiskerLeft _ (OplaxPullback.llm _ _)

  abbrev rrm : projMid L R ⟶ projRight L R ⋙ R
    := whiskerLeft _ (OplaxPullback.rrm _ _)

  noncomputable def mrr : projRight L R ⋙ R ⟶ projMid L R where
    app o := inv _ (I := o.property)

  noncomputable def rrem : projMid L R ≅ projRight L R ⋙ R where
    hom := rrm _ _
    inv := mrr _ _
    hom_inv_id := by unfold rrm ; unfold mrr ; aesop
    inv_hom_id := by unfold rrm ; unfold mrr ; aesop

  noncomputable abbrev natTrans : projRight L R ⋙ R ⟶ projLeft L R ⋙ L
    := mrr _ _ ≫ llm _ _

  variable {L R}

  def from_comma : Comma R L ⥤ FullSubcategory (CommaRight L R)
    := CommaLeft.from_comma ⋙ (comma_left_right R L).functor

  @[simp] lemma from_comma_projLeft  : from_comma ⋙ projLeft  L R = Comma.snd R L := rfl
  @[simp] lemma from_comma_projRight : from_comma ⋙ projRight L R = Comma.fst R L := rfl
  @[simp] lemma from_comma_inclusion : from_comma ⋙ fullSubcategoryInclusion (CommaRight L R) = OplaxPullback.from_comma R L ⋙ OplaxPullback.flip := rfl

  noncomputable def to_comma : FullSubcategory (CommaRight L R) ⥤ Comma R L
    := (comma_left_right R L).inverse ⋙ CommaLeft.to_comma

  @[simp] lemma to_comma_fst : to_comma ⋙ Comma.snd R L = projLeft  L R := rfl
  @[simp] lemma to_comma_snd : to_comma ⋙ Comma.fst R L = projRight L R := rfl

  noncomputable def from_to_inverse : from_comma ⋙ to_comma ≅ 𝟭 (Comma R L)
    := CommaLeft.from_to_inverse

  noncomputable def to_from_inverse : to_comma ⋙ from_comma ≅ 𝟭 (FullSubcategory (CommaRight L R))
    := isoWhiskerLeft (comma_left_right R L).inverse (isoWhiskerRight CommaLeft.to_from_inverse (comma_left_right R L).functor)

  noncomputable def to_from_inclusion : to_comma ⋙ OplaxPullback.from_comma R L ⋙ OplaxPullback.flip ≅ fullSubcategoryInclusion (CommaRight L R)
    := isoWhiskerRight (isoWhiskerLeft (comma_left_right R L).inverse CommaLeft.to_from_inclusion) flip

  noncomputable def equiv_comma : FullSubcategory (CommaRight L R) ≌ Comma R L
    := Equivalence.mk to_comma from_comma to_from_inverse.symm from_to_inverse

end CommaRight
