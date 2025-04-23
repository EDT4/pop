import Mathlib.CategoryTheory.Comma.Basic
import Pop.CategoryTheory.CommaExtras
import Pop.CategoryTheory.OplaxPullback

namespace CategoryTheory.OplaxPullback

open CategoryTheory

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable {D : Type _} [Category D]
variable (L : A ⥤ C)
variable (R : B ⥤ C)

@[simps!]
def from_comma : Comma L R ⥤ OplaxPullback L R
  := liftL (Comma.fst L R) (Comma.snd L R) (Comma.natTrans L R)

@[simp] def from_comma_projLeft  : from_comma L R ⋙ projLeft  L R = Comma.fst L R := rfl
@[simp] def from_comma_projRight : from_comma L R ⋙ projRight L R = Comma.snd L R := rfl
