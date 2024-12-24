require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1321091 : Prf (∀ (λ x : El hreal, (∀ (λ y : El hreal, (∀ (λ z : El hreal, (= (hreal_mul x (hreal_add y z)) (hreal_add (hreal_mul x y) (hreal_mul x z)))))))));
