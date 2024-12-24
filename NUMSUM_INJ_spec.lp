require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1054431 : Prf (∀ (λ b1 : El bool, (∀ (λ x1 : El num, (∀ (λ b2 : El bool, (∀ (λ x2 : El num, (= (= (NUMSUM b1 x1) (NUMSUM b2 x2)) (∧ (= b1 b2) (= x1 x2)))))))))));
