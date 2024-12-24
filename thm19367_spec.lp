require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem19367 (a : El bool) (b : El bool) (c : El bool) : Prf (= (∧ (∨ a b) c) (∨ (∧ a c) (∧ b c)));
