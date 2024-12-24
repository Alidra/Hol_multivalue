require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1320816 : Prf (∀ (λ x : El hreal, (∀ (λ y : El hreal, (∀ (λ z : El hreal, (= (hreal_mul x (hreal_mul y z)) (hreal_mul (hreal_mul x y) z))))))));
