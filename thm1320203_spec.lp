require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1320203 : Prf (∀ (λ x : El hreal, (∀ (λ y : El hreal, (∀ (λ z : El hreal, (= (hreal_add x (hreal_add y z)) (hreal_add (hreal_add x y) z))))))));
