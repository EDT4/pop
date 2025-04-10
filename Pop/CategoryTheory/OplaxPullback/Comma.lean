import Mathlib.CategoryTheory.Comma.Basic
import Pop.CategoryTheory.OplaxPullback

namespace CategoryTheory.OplaxPullback

open CategoryTheory

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable (L : A ⥤ C)
variable (R : B ⥤ C)

@[simps!]
def from_comma : Comma L R ⥤ OplaxPullback L R
  := liftL (Comma.fst L R) (Comma.snd L R) (Comma.natTrans L R)

@[simps!]
def from_flipped_comma : Comma R L ⥤ OplaxPullback L R
  := liftR (Comma.snd R L) (Comma.fst R L) (Comma.natTrans R L)

-- Partially-oplax pullback (on the left).
-- `OplaxPullback`s where `homl` is an isomorphism.
def CommaLeft : Set (OplaxPullback L R) := fun p => IsIso p.homl

namespace CommaLeft
  def from_comma : Comma L R ⥤ FullSubcategory (CommaLeft L R)
    := FullSubcategory.lift
      (CommaLeft L R)
      (OplaxPullback.from_comma L R)
      (by simp [OplaxPullback.from_comma,CommaLeft] ; infer_instance)

  noncomputable def to_comma : FullSubcategory (CommaLeft L R) ⥤ Comma L R where
    obj p := {
      left := p.obj.left
      right := p.obj.right
      hom := inv _ (I := p.property) ≫ p.obj.homr
    }
    map f := {
      left := f.left
      right := f.right
    }

  -- TODO: Not really difficult proofs, but they are long due to the almost identical cases and I guess inv not being easy to simp? If naively automated, a timeout is reached.
  noncomputable def from_to_inverse : from_comma L R ⋙ to_comma L R ≅ 𝟭 (Comma L R) := NatIso.ofComponents
    (fun _ => {
      hom := {
        left  := 𝟙 _
        right := 𝟙 _
        w := by
          dsimp [from_comma,to_comma]
          rw [Functor.map_id,Functor.map_id,IsIso.inv_id,Category.comp_id,Category.id_comp]
        }
      inv := {
        left  := 𝟙 _
        right := 𝟙 _
        w := by
          dsimp [from_comma,to_comma]
          rw [Functor.map_id,Functor.map_id,IsIso.inv_id,Category.comp_id,Category.id_comp,Category.id_comp]
      }
    })
    (by intros ; ext <;> (dsimp [to_comma,from_comma] ; rw [Category.comp_id,Category.id_comp]))

  noncomputable def to_from_inverse : to_comma L R ⋙ from_comma L R ≅ 𝟭 _ := NatIso.ofComponents
    (fun x => {
      hom := {
        left   := 𝟙 _
        middle := inv x.obj.homl (I := x.property)
        right  := 𝟙 _
        wl := by
          dsimp [from_comma,to_comma]
          rw [Functor.map_id,Category.comp_id,IsIso.inv_hom_id]
        wr := by
          dsimp [from_comma,to_comma]
          rw [Functor.map_id,Category.comp_id,IsIso.eq_inv_comp,← Category.assoc,IsIso.hom_inv_id,Category.id_comp]
      }
      inv := {
        left   := 𝟙 _
        middle := x.obj.homl
        right  := 𝟙 _
        wl := by
          dsimp [from_comma,to_comma]
          rw [Functor.map_id,Category.comp_id]
        wr := by
          dsimp [from_comma,to_comma]
          rw [Functor.map_id,Category.comp_id,← Category.assoc,IsIso.hom_inv_id,Category.id_comp]
      }
      hom_inv_id := Hom.ext
        (by
          apply (Eq.trans (OplaxPullback.category_comp_left _ _) ·)
          apply (Eq.trans · (OplaxPullback.category_id_left _))
          dsimp [from_comma,to_comma]
          rw [Category.id_comp]
        )
        (by
          apply (Eq.trans (OplaxPullback.category_comp_middle _ _) ·)
          apply (Eq.trans · (OplaxPullback.category_id_middle _))
          dsimp [from_comma,to_comma]
          rw [IsIso.inv_hom_id]
        )
        (by
          apply (Eq.trans (OplaxPullback.category_comp_right _ _) ·)
          apply (Eq.trans · (OplaxPullback.category_id_right _))
          dsimp [from_comma,to_comma]
          rw [Category.id_comp]
        )
      inv_hom_id := Hom.ext
        (by
          apply (Eq.trans (OplaxPullback.category_comp_left   _ _) ·)
          apply (Eq.trans · (OplaxPullback.category_id_left _))
          dsimp [from_comma,to_comma]
          rw [Category.id_comp]
        )
        (by
          apply (Eq.trans (OplaxPullback.category_comp_middle _ _) ·)
          apply (Eq.trans · (OplaxPullback.category_id_middle _))
          dsimp [from_comma,to_comma]
          rw [IsIso.hom_inv_id]
        )
        (by
          apply (Eq.trans (OplaxPullback.category_comp_right  _ _) ·)
          apply (Eq.trans · (OplaxPullback.category_id_right _))
          dsimp [from_comma,to_comma]
          rw [Category.id_comp]
        )
    })
    (fun f => Hom.ext
      (by
        apply (Eq.trans (OplaxPullback.category_comp_left   _ _) ·)
        apply (Eq.trans · (OplaxPullback.category_comp_left   _ _))
        dsimp [from_comma,to_comma]
        rw [Category.comp_id,Category.id_comp]
      )
      (by
        apply (Eq.trans (OplaxPullback.category_comp_middle   _ _) ·)
        apply (Eq.trans · (OplaxPullback.category_comp_middle   _ _))
        dsimp [from_comma,to_comma]
        rw [IsIso.comp_inv_eq,Category.assoc,IsIso.eq_inv_comp,f.wl]
      )
      (by
        apply (Eq.trans (OplaxPullback.category_comp_right   _ _) ·)
        apply (Eq.trans · (OplaxPullback.category_comp_right   _ _))
        dsimp [from_comma,to_comma]
        rw [Category.comp_id,Category.id_comp]
      )
    )

  noncomputable def equiv_comma : FullSubcategory (CommaLeft L R) ≌ Comma L R
    := Equivalence.mk
      (to_comma L R)
      (from_comma L R)
      (to_from_inverse L R).symm
      (from_to_inverse L R)

end CommaLeft

-- Partially-oplax pullback (on the right).
-- `OplaxPullback`s where `homr` is an isomorphism.
def CommaRight : Set (OplaxPullback L R) := CommaLeft R L ∘ flip.obj

def comma_left_right : FullSubcategory (CommaLeft L R) ⥤ FullSubcategory (CommaRight R L)
  := FullSubcategory.lift _ (fullSubcategoryInclusion _ ⋙ flip) FullSubcategory.property

def comma_right_left : FullSubcategory (CommaRight L R) ⥤ FullSubcategory (CommaLeft R L)
  := FullSubcategory.lift _ (fullSubcategoryInclusion _ ⋙ flip) FullSubcategory.property

def comma_left_right_right_left : comma_left_right L R ⋙ comma_right_left R L ≅ 𝟭 _
  := NatIso.ofComponents (fun _ => Iso.refl _)

def comma_right_left_left_right : comma_right_left L R ⋙ comma_left_right R L ≅ 𝟭 _
  := NatIso.ofComponents (fun _ => Iso.refl _)

namespace CommaRight
  def from_comma : Comma R L ⥤ FullSubcategory (CommaRight L R)
    := CommaLeft.from_comma R L ⋙ comma_left_right R L

  noncomputable def to_comma : FullSubcategory (CommaRight L R) ⥤ Comma R L
    := comma_right_left L R ⋙ CommaLeft.to_comma R L

  noncomputable def from_to_inverse : from_comma L R ⋙ to_comma L R ≅ 𝟭 (Comma R L)
    := CommaLeft.from_to_inverse R L

  noncomputable def to_from_inverse : to_comma L R ⋙ from_comma L R ≅ 𝟭 (FullSubcategory (CommaRight L R))
    := isoWhiskerLeft (comma_right_left L R) (isoWhiskerRight (CommaLeft.to_from_inverse R L) (comma_left_right R L))

  noncomputable def equiv_comma : FullSubcategory (CommaRight L R) ≌ Comma R L
    := Equivalence.mk
      (to_comma L R)
      (from_comma L R)
      (to_from_inverse L R).symm
      (from_to_inverse L R)

end CommaRight

-- Pullback.
-- `OplaxPullback`s where both `homl` and `homr` are isomorphisms.
def CommaLeftRight : Set (OplaxPullback L R) := (CommaLeft L R) ∩ (CommaRight L R)
def PullbackComma : Set (Comma L R) := fun p => IsIso p.hom

noncomputable def PullbackComma.flip : FullSubcategory (PullbackComma L R) ⥤ FullSubcategory (PullbackComma R L) where
  obj o := {
    obj := {
      left  := o.obj.right
      right := o.obj.left
      hom   := inv o.obj.hom (I := o.property)
    }
    property := let _ : IsIso o.obj.hom := o.property ; IsIso.inv_isIso
  }
  map f := {
    left  := f.right
    right := f.left
    w     := by rw [IsIso.comp_inv_eq,Category.assoc,IsIso.eq_inv_comp,f.w]
  }

namespace CommaLeftRight
  def from_comma : FullSubcategory (PullbackComma L R) ⥤ FullSubcategory (CommaLeftRight L R)
    := FullSubcategory.lift (CommaLeftRight L R)
      (fullSubcategoryInclusion _ ⋙ OplaxPullback.from_comma L R)
      fun o =>
        ⟨ ((CommaLeft.from_comma L R).obj o.obj).property
        , by
          let tte := ((PullbackComma.flip L R).obj o).obj
          let t := ((CommaRight.from_comma L R).obj sorry).property
          dsimp [OplaxPullback.from_comma,CommaRight.from_comma] at *
          exact t
        ⟩

end CommaLeftRight
