require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7249 (B : El bool) (A : El bool) (C : El bool) (D : El bool) (h1 : Prf (∧ (⇒ B A) (⇒ C D))) : Prf (⇒ (⇒ A C) (⇒ B D));
