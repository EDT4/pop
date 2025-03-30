import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic.ApplyFun

open CategoryTheory

namespace CategoryTheory.Adjunction.CoreEtaInvertibleHom
  variable {C₁ C₂ : Type _}
  variable [Category C₁]
  variable [Category C₂]
  variable {L : Functor C₁ C₂}
  variable {R : Functor C₂ C₁}
  variable (η : 𝟭 C₁ ⟶ L ⋙ R)

  abbrev hom {c₁ : C₁} {c₂ : C₂} : (L.obj c₁ ⟶ c₂) → (c₁ ⟶ R.obj c₂)
    := fun f => η.app c₁ ≫ R.map f

  def mk
    -- TODO: So, to construct such an invHom: let L, R be fully faithful, but the functors are not bijective? So...
    -- TODO: The assumptions here is Function.Bijective but using inverses and Mathlib.Logic.Equiv.Defs.Equiv but with a parameter. There is no "IsEquiv"?
    (invHom : ∀{c₁ : C₁}{c₂ : C₂}, (c₁ ⟶ R.obj c₂) → (L.obj c₁ ⟶ c₂))
    (left_inv  : ∀{c₁}{c₂}, Function.LeftInverse  invHom (hom η (c₁ := c₁) (c₂ := c₂)))
    (right_inv : ∀{c₁}{c₂}, Function.RightInverse invHom (hom η (c₁ := c₁) (c₂ := c₂)))
    : L ⊣ R
    :=
      Adjunction.mkOfHomEquiv {
        homEquiv := fun _ _ => .mk (hom η) invHom left_inv right_inv
        homEquiv_naturality_left_symm := by
          intro c₁₁ c₁₂ c₂ f g
          simp
          apply_fun hom η
          . rw [right_inv]
            simp [hom]
            rewrite [← Category.assoc , ← Functor.comp_map , ← η.naturality f]
            simp
            congr
            change g = hom η (invHom g)
            rw [right_inv]
          . exact Function.LeftInverse.injective left_inv
        homEquiv_naturality_right := by simp [hom]
      }

  -- TODO: temporary
  noncomputable def mkBijective (bij : ∀{c₁}{c₂}, Function.Bijective (hom η (c₁ := c₁) (c₂ := c₂))) : L ⊣ R :=
    let e {c₁}{c₂} := Equiv.ofBijective (hom η (c₁ := c₁) (c₂ := c₂)) bij
    mk η e.invFun e.left_inv e.right_inv
end CategoryTheory.Adjunction.CoreEtaInvertibleHom

namespace CategoryTheory.Adjunction.FullyFaithfulIso
  variable {C : Type _}
  variable [Category C]
  variable {D : Type _}
  variable [Category D]

  noncomputable def mk
    (T : C ⥤ D)
    (u : D ⥤ C)
    [fu : u.Full]
    [ff : u.Faithful]
    (η : 𝟭 C ⟶ T ⋙ u)
    [i : ∀(d : D), IsIso (η.app (u.obj d))]
    : T ⊣ u :=
    let ε := .mk
      (fun d => Functor.preimage u (inv _ (I := i d)))
      (by
        intro X Y f
        simp_all
        apply_fun u.map
        . simp only [Functor.map_comp, Functor.map_preimage, IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
          apply (Eq.trans · (η.naturality (u.map f)).symm)
          apply congr_arg (η.app (u.obj X) ≫ ·)
          simp only [Functor.comp_obj, Functor.comp_map]
        . exact ff.map_injective
      )
    {
      unit := η
      counit := ε
      left_triangle_components := by
        intro c
        simp only [Functor.id_obj, Functor.comp_obj]
        apply_fun u.map
        . simp only [Functor.map_comp, Functor.map_preimage, Functor.map_id, IsIso.comp_inv_eq, Category.id_comp, ε]
          apply_fun (η.app c ≫ ·)
          . exact (η.naturality (η.app c)).symm
          . sorry -- TODO: probably not?
        . exact ff.map_injective
      right_triangle_components := by simp only [Functor.id_obj, Functor.map_preimage, IsIso.hom_inv_id, implies_true, ε]
    }
