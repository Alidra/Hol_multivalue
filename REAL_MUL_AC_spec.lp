require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1486340 (n : El real) (m : El real) (p : El real) : Prf (∧ (= (real_mul m n) (real_mul n m)) (∧ (= (real_mul (real_mul m n) p) (real_mul m (real_mul n p))) (= (real_mul m (real_mul n p)) (real_mul n (real_mul m p)))));
