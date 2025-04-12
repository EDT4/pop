import Mathlib.CategoryTheory.Comma.Basic
import Pop.CategoryTheory.IsoComma
import Pop.CategoryTheory.OplaxPullback
import Pop.CategoryTheory.OplaxPullback.Comma

namespace CategoryTheory.OplaxPullback

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable (L : A ⥤ C)
variable (R : B ⥤ C)

-- `OplaxPullback`s where both `homl` and `homr` are isomorphisms.
def CommaLeftRight : Set (OplaxPullback L R) := (CommaLeft L R) ∩ (CommaRight L R)

namespace CommaLeftRight
  variable {L R}

  def from_isoComma : IsoComma L R ⥤ FullSubcategory (CommaLeftRight L R)
    := FullSubcategory.lift (CommaLeftRight L R)
      (IsoComma.rightComma ⋙ OplaxPullback.from_comma _ _)
      (fun o => ⟨IsIso.id (L.obj o.left) , o.iso.isIso_hom⟩)

  noncomputable def to_isoComma : FullSubcategory (CommaLeftRight L R) ⥤ IsoComma L R
    := IsoComma.lift
      (fullSubcategoryInclusion _ ⋙ OplaxPullback.leftFunctor _ _)
      (fullSubcategoryInclusion _ ⋙ OplaxPullback.rightFunctor _ _)
      {
        hom := (Functor.associator _ _ _).hom ≫ OplaxPullback.CommaLeft.natInv                    (fun _ => And.left)  ≫ whiskerLeft (fullSubcategoryInclusion (CommaLeftRight L R)) (OplaxPullback.rrm L R) ≫ (Functor.associator _ _ _).inv
        inv := (Functor.associator _ _ _).hom ≫ OplaxPullback.CommaRight.natInv (L := L) (R := R) (fun _ => And.right) ≫ whiskerLeft (fullSubcategoryInclusion (CommaLeftRight L R)) (OplaxPullback.llm L R) ≫ (Functor.associator _ _ _).inv
        hom_inv_id := by ext ; simp [CommaLeft.natInv,CommaRight.natInv]
        inv_hom_id := by ext ; simp [CommaLeft.natInv,CommaRight.natInv]
      }

  noncomputable def from_to_inverse : from_isoComma ⋙ to_isoComma ≅ 𝟭 (IsoComma R L)
    := by
      dsimp [to_isoComma,from_isoComma,CommaLeft.natInv,CommaRight.natInv]
      exact NatIso.ofComponents
        (fun o => {
          hom := {left := 𝟙 _ , right := 𝟙 _}
          inv := {left := 𝟙 _ , right := 𝟙 _}
          hom_inv_id := by apply IsoComma.Hom.ext <;> simp
          inv_hom_id := by apply IsoComma.Hom.ext <;> simp
        })
        (by intro _ _ _ ; apply IsoComma.Hom.ext <;> aesop)

  noncomputable def to_from_inverse : to_isoComma ⋙ from_isoComma ≅ 𝟭 (FullSubcategory (CommaLeftRight L R))
    := by
      dsimp [to_isoComma,from_isoComma,CommaLeft.natInv,CommaRight.natInv]
      exact NatIso.ofComponents
        (fun o => {
          hom := {left := 𝟙 _ , middle := inv o.obj.homl (I := And.left o.property) , right := 𝟙 _}
          inv := {left := 𝟙 _ , middle := o.obj.homl , right := 𝟙 _}
          hom_inv_id := by apply Hom.ext <;> (dsimp only [(·≫·)] ; simp ; rfl)
          inv_hom_id := by apply Hom.ext <;> (dsimp only [(·≫·)] ; simp ; rfl)
        })
        (by intro _ _ _ ;apply Hom.ext <;> (dsimp only [(·≫·)] ; simp))

  noncomputable def equiv_isoComma : FullSubcategory (CommaLeftRight L R) ≌ IsoComma L R
    := Equivalence.mk
      to_isoComma
      from_isoComma
      to_from_inverse.symm
      from_to_inverse

end CommaLeftRight
