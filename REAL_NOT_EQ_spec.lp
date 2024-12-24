require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1495214 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (¬ (= x y)) (∨ (real_lt x y) (real_lt y x)))))));
