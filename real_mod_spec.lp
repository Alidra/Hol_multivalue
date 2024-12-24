require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2428623 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ n : El real, (= (real_mod n x y) (∃ (λ q : El real, (∧ (integer q) (= (real_sub x y) (real_mul q n))))))))))));
