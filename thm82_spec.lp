require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem82 (P : El bool) : Prf (⇒ (¬ P) (= P F));
