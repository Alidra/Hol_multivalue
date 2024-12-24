require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1281249 : Prf (∀ (λ x : El nadd, (∀ (λ y : El nadd, (∀ (λ z : El nadd, (⇒ (nadd_le x y) (nadd_le (nadd_mul x z) (nadd_mul y z)))))))));
