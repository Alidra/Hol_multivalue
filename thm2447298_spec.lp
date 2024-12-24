require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2447298 (b : El int) (a : El int) : Prf (= ((λ a' : El int, (= (int_divides a' b) (∃ (λ x : El int, (= b (int_mul a' x)))))) a) (= (int_divides a b) (∃ (λ x : El int, (= b (int_mul a x))))));
