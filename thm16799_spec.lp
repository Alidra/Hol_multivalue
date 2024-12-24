require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem16799 (a : El bool) (b : El bool) (h1 : Prf (¬ a)) (h2 : Prf (¬ b)) : Prf (¬ (∨ a b));
