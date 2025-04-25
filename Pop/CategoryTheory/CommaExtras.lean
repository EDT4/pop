import Mathlib.CategoryTheory.Comma.Basic

namespace CategoryTheory.Comma

open CategoryTheory

variable {A : Type _} [Category A]
variable {B : Type _} [Category B]
variable {C : Type _} [Category C]
variable {D : Type _} [Category D]
variable {L : A ⥤ C}
variable {R : B ⥤ C}
variable {da : D ⥤ A}
variable {db : D ⥤ B}
variable {dp : (da ⋙ L) ⟶ (db ⋙ R)}
variable {F G : D ⥤ Comma L R}

@[simps]
def lift
  (da : D ⥤ A)
  (db : D ⥤ B)
  (dp : (da ⋙ L) ⟶ (db ⋙ R))
  : D ⥤ Comma L R
where
  obj d := {
    left   := da.obj d
    right  := db.obj d
    hom    := dp.app d
  }
  map f := {
    left  := da.map f
    right := db.map f
    w  := dp.naturality _
  }

@[simp] def lift_fst : lift da db dp ⋙ fst L R = da := rfl
@[simp] def lift_snd : lift da db dp ⋙ snd L R = db := rfl
@[simp] def lift_fst_snd : lift (fst L R) (snd L R) (natTrans L R) = 𝟭 _ := rfl
@[simp] def lift_natTrans : whiskerLeft (lift da db dp) (natTrans L R) = dp := rfl

@[simps!]
def liftTrans
  (ta : F ⋙ fst L R ⟶ G ⋙ fst L R)
  (tb : F ⋙ snd L R ⟶ G ⋙ snd L R)
  (h : whiskerRight ta L ≫ whiskerLeft G (Comma.natTrans _ _) = whiskerLeft F (Comma.natTrans _ _) ≫ whiskerRight tb R)
  : F ⟶ G where
  app d := {
    left  := ta.app d
    right := tb.app d
    w := congrArg (fun f => f.app d) h
  }
  naturality x y f := by
    ext
    . exact ta.naturality f
    . exact tb.naturality f

def lift_ext
  (α β : F ⟶ G)
  (hfst : whiskerRight α (fst L R) = whiskerRight β (fst L R))
  (hsnd : whiskerRight α (snd L R) = whiskerRight β (snd L R))
  : α = β := by
    ext d
    · let p := congrArg (fun f => f.app d) hfst ; simp at p ; exact p
    · let p := congrArg (fun f => f.app d) hsnd ; simp at p ; exact p

@[simps!]
def liftIso
  (ta : F ⋙ fst L R ≅ G ⋙ fst L R)
  (tb : F ⋙ snd L R ≅ G ⋙ snd L R)
  (hl : whiskerRight ta.inv L ≫ whiskerLeft F (Comma.natTrans _ _) = whiskerLeft G (Comma.natTrans _ _) ≫ whiskerRight tb.inv R)
  (hr : whiskerRight ta.hom L ≫ whiskerLeft G (Comma.natTrans _ _) = whiskerLeft F (Comma.natTrans _ _) ≫ whiskerRight tb.hom R)
  : F ≅ G where
  hom := liftTrans ta.hom tb.hom hr
  inv := liftTrans ta.inv tb.inv hl
  hom_inv_id := by apply lift_ext <;> simp [liftTrans,liftTrans,whiskerRight]
  inv_hom_id := by apply lift_ext <;> simp [liftTrans,liftTrans,whiskerRight]

-- def lift_unique
--   (F : D ⥤ Comma L R)
--   (ffst : F ⋙ fst L R ≅ da)
--   (fsnd : F ⋙ snd L R ≅ db)
--   : F ≅ lift da db dp
--   := liftIso'
--     (by simp only [lift_fst] ; exact ffst)
--     (by simp only [lift_snd] ; exact fsnd)
--     sorry
--     sorry
