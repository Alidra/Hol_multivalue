require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3117508 (a : El num) (b : El num) : Prf (= ((λ b' : El num, (= (num_divides a b') (int_divides (int_of_num a) (int_of_num b')))) b) (= (num_divides a b) (int_divides (int_of_num a) (int_of_num b))));
