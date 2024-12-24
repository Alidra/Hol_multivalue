require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2305894 (n : El int) (m : El int) (p : El int) : Prf (∧ (= (int_mul (int_mul m n) p) (int_mul m (int_mul n p))) (= (int_mul m (int_mul n p)) (int_mul n (int_mul m p))));
