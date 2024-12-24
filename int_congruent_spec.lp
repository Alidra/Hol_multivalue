require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2437518 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ n : El int, (= ((@== int) x y (int_mod n)) (∃ (λ d : El int, (= (int_sub x y) (int_mul n d)))))))))));
