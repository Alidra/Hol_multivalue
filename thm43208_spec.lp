require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem43208 (B : El bool) (D : El bool) (A : El bool) (C : El bool) : Prf (⇒ (∧ (⇒ B A) (⇒ B (⇒ D C))) (⇒ (∧ B D) (∧ A C)));
