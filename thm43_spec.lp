require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem43 (q : El bool) (p : El bool) : Prf (⇒ (= p q) (⇒ q p));
