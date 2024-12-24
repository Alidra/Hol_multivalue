require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem20828 (b : El bool) (a : El bool) (h1 : Prf (= a F)) : Prf (= (= (¬ (∨ F b)) (∧ (¬ F) (¬ b))) (= (¬ (∨ a b)) (∧ (¬ a) (¬ b))));
