require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7130 (A : El bool) (C : El bool) (B : El bool) (D : El bool) : Prf (⇒ (∧ (⇒ A B) (⇒ C D)) (⇒ (∨ A C) (∨ B D)));
