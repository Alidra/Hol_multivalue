require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2305379 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∧ (int_le x (int_max x y)) (int_le y (int_max x y)))))));
