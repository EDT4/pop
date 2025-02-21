import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity

universe u

def Nat.even_add_two
  {n : ℕ}
  : Even (n + 2) ↔ Even n
  := (Nat.even_add (n := 2)).trans (.intro (fun p => p.mpr even_two) (fun p => .intro (fun _ => even_two) (fun _ => p)))

theorem Nat.even_add_one' {n : ℕ} : ¬Even n.succ ↔ Even n
  := Nat.even_add_one.symm.trans Nat.even_add_two

-- TODO: More difficult to prove stuff by this type of recursion?
def Nat.rec2
  {A : ℕ → Sort u}
  (zero : A 0)
  (succ0 : (n : ℕ) →  Even n → A n → A n.succ)
  (succ1 : (n : ℕ) → ¬Even n → A n → A n.succ)
  : (n : Nat) → A n
  | 0     => zero
  | n + 1 => Nat.rec2
    (A := fun n => A n.succ)
    (succ0 0 Even.zero zero)
    (fun n e => succ1 n.succ (Nat.even_add_one'.mpr e))
    (fun n e => succ0 n.succ (Nat.even_add_one.mpr e))
    n

-- def Nat.rec2.even_case
--   {A : ℕ → Sort u}
--   {zero : A 0}
--   {succ0 : (n : ℕ) → Even n → A n → A n.succ}
--   {succ1 : (n : ℕ) → ¬Even n → A n → A n.succ}
--   {n : ℕ} (p :  Even n)
--   : Nat.rec2 zero succ0 succ1 n.succ.succ = succ1 n.succ (Nat.even_add_one'.mpr p) (succ0 n p (Nat.rec2 zero succ0 succ1 n))
--   := sorry

-- TODO: Probably not a good way of doing this
def Nat.rec2_even_case
  {A : ℕ → Sort u}
  {zero : A 0}
  {succ0 : (n : ℕ) → Even n → A n → A n.succ}
  {succ1 : (n : ℕ) → ¬Even n → A n → A n.succ}
  {n : ℕ} (p :  Even n)
  : Nat.rec2 zero succ0 succ1 n.succ = succ0 n p (Nat.rec2 zero succ0 succ1 n)
  :=
    let r := Nat.rec2 zero succ0 succ1
    -- TODO: Requires stronger recursion
    Nat.rec2 (A := fun n => (p : Even n) → r n.succ = succ0 n p (r n))
      (fun _ => rfl)
      (fun _ p1 _ p2 => (Nat.even_add_one.mp p2 p1).elim)
      (fun n o p e => sorry) n p

def Nat.rec2_odd_case
  {A : ℕ → Sort u}
  {zero : A 0}
  {succ0 : (n : ℕ) → Even n → A n → A n.succ}
  {succ1 : (n : ℕ) → ¬Even n → A n → A n.succ}
  {n : ℕ} (p :  ¬Even n)
  : Nat.rec2 zero succ0 succ1 n.succ = succ1 n p (Nat.rec2 zero succ0 succ1 n)
  := sorry





def Nat.rec2'
  {A : ℕ → Sort u}
  (zero : A 0)
  (succ0 : (n : ℕ) →  Even n → A n → A n.succ)
  (succ1 : (n : ℕ) → ¬Even n → A n → A n.succ)
  : (n : Nat) → A n
  := Nat.rec
    zero
    (fun n r => Decidable.casesOn (Nat.instDecidablePredEven n)
      (fun (p : ¬Even n) => succ1 n p r)
      (fun (p :  Even n) => succ0 n p r)
    )

def Nat.rec2'_even_case
  {A : ℕ → Sort u}
  {zero : A 0}
  {succ0 : (n : ℕ) → Even n → A n → A n.succ}
  {succ1 : (n : ℕ) → ¬Even n → A n → A n.succ}
  {n : ℕ} (p :  Even n)
  : Nat.rec2' zero succ0 succ1 n.succ = succ0 n p (Nat.rec2' zero succ0 succ1 n)
  :=
    let r := Nat.rec2' zero succ0 succ1
    Nat.rec2' (A := fun n => (p : Even n) → r n.succ = succ0 n p (r n))
      (fun _ => rfl)
      (fun _ p1 _ p2 => (Nat.even_add_one.mp p2 p1).elim)
      (fun n o p e => by exact Decidable.casesOn (Nat.instDecidablePredEven n) (fun o2 => sorry) (by aesop)) -- TODO: How to prove on casesOn?
      n p

-- TODO: There is also this one, but the recursion looks weird? https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/EvenOddRec.html#Nat.evenOddRec
