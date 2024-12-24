require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1720940 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (= (= x y) (∧ (= (real_sgn x) (real_sgn y)) (= (real_abs x) (real_abs y))))))));
