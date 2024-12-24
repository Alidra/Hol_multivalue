require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem21007 (a : El bool) (b : El bool) : Prf (= (∨ (¬ a) (¬ b)) (¬ (∧ a b)));
