require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2522863 : Prf (∀ (λ m : El int, (∀ (λ n : El int, (∀ (λ p : El int, (= (= (rem m p) (rem n p)) ((@== int) m n (int_mod p)))))))));
