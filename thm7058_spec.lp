require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7058 (A : El bool) (B : El bool) (C : El bool) (D : El bool) (h1 : Prf (∧ (⇒ A B) (⇒ C D))) : Prf (⇒ (∧ A C) (∧ B D));
