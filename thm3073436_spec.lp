require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3073436 (b : El num) (a : El num) : Prf (= (= (∃ (λ x : El int, (= (int_of_num b) (int_mul (int_of_num a) x)))) (∃ (λ x : El num, (= b (* a x))))) (= (num_divides a b) (∃ (λ x : El num, (= b (* a x))))));
