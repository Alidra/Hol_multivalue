require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2305316 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (= (int_le (int_max x y) z) (∧ (int_le x z) (int_le y z)))))))));
