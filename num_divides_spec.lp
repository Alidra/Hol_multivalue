require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2836659 : Prf (∀ (λ a : El num, (∀ (λ b : El num, (= (num_divides a b) (int_divides (int_of_num a) (int_of_num b)))))));
