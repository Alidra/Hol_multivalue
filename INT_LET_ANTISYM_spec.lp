require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2302114 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (¬ (∧ (int_le x y) (int_lt y x)))))));
