require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem21596 (b : El bool) (a : El bool) (h1 : Prf (= a T)) : Prf (⇒ (= a b) (∨ b (¬ a)));
