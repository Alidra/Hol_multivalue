require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem19490 (b : El bool) (a : El bool) (c : El bool) : Prf (= (∨ a (∧ b c)) (∧ (∨ a b) (∨ a c)));
