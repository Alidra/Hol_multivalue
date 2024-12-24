require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem21595 (b : El bool) (a : El bool) (h1 : Prf (= a F)) : Prf (⇒ (= a b) (∨ b (¬ a)));
