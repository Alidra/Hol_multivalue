require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem20862 (b : El bool) : Prf (= (¬ (∨ T b)) (∧ (¬ T) (¬ b)));
