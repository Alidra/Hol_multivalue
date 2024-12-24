require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3074597 (b : El num) (a : El num) : Prf (= (num_divides a b) (∃ (λ x : El num, (= b (* a x)))));
