import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

open CategoryTheory
open CategoryTheory.ObjectProperty

namespace CategoryTheory

variable {C : Type _}  [Category C]
variable {C₁ : Type _} [Category C₁]
variable {C₂ : Type _} [Category C₂]
variable {F G : Functor C₁ C₂}

def natIso_isClosedUnderIso (t : NatTrans F G) : IsClosedUnderIsomorphisms (fun x => IsIso (t.app x)) where
  of_iso e _ := IsIso.of_isIso_fac_left (t.naturality e.hom)

theorem comp_inv_eq_inv_comp
  {x y : C} (f₁ g₁ : x ⟶ y) [i₁ : IsIso g₁]  {f₂ g₂ : y ⟶ x} [i₂ : IsIso g₂]
  : (f₁ ≫ inv g₁ = inv g₂ ≫ f₂) ↔ (g₂ ≫ f₁ = f₂ ≫ g₁)
  := by rw [IsIso.comp_inv_eq,Category.assoc,IsIso.eq_inv_comp]
