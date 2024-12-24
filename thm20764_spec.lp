require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem20764 (b : El bool) (a : El bool) : Prf (= (∨ a b) (⇒ (¬ b) a));
