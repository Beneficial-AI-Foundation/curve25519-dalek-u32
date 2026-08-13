import Aeneas

/-!
# Aeneas.Std extensions, candidates for upstreaming

-/

open Aeneas.Std

def Aeneas.Std.Array.map {α β : Type} {n : Usize} (f : α → β) (a : Array α n) :
    Array β n :=
  ⟨a.val.map f, by simp⟩

@[simp, simp_lists]
theorem Aeneas.Std.Array.val_map {α β : Type} {n : Usize} (f : α → β) (a : Array α n) :
    (a.map f).val = a.val.map f := rfl
