require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem13354 (A : El bool) (C : El bool) (b : El bool) (B : El bool) (D : El bool) : Prf (⇒ (∧ (⇒ A B) (⇒ C D)) (⇒ ((@COND bool) b A C) ((@COND bool) b B D)));
