require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1501119 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (= (real_le (real_add x z) (real_add y z)) (real_le x y))))))));
