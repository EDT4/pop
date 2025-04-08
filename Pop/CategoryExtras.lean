import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

open CategoryTheory
open CategoryTheory.ObjectProperty

namespace CategoryTheory

variable {C₁ : Type _} [Category C₁]
variable {C₂ : Type _} [Category C₂]
variable {F G : Functor C₁ C₂}

def natIso_isClosedUnderIso (t : NatTrans F G) : IsClosedUnderIsomorphisms (fun x => IsIso (t.app x)) where
  of_iso e i := by
    obtain ⟨f,⟨l,r⟩⟩ := i
    iterate 3 constructor
    . rw [← Category.assoc,← t.naturality e.inv,Category.assoc,← Category.assoc (t.app _),l,Category.id_comp,← Functor.map_comp,e.inv_hom_id,Functor.map_id]
    . rw [Category.assoc,Category.assoc,t.naturality e.hom,← Category.assoc f,r,Category.id_comp,← Functor.map_comp,e.inv_hom_id,Functor.map_id]
    -- Explicit inverse to (t.app Y): G.map e.inv ≫ f ≫ F.map e.hom
