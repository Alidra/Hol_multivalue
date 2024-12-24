require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7250 (A : El bool) (C : El bool) (B : El bool) (D : El bool) : Prf (⇒ (∧ (⇒ B A) (⇒ C D)) (⇒ (⇒ A C) (⇒ B D)));
