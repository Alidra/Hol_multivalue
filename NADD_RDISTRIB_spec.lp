require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1285826 : Prf (∀ (λ x : El nadd, (∀ (λ y : El nadd, (∀ (λ z : El nadd, (nadd_eq (nadd_mul (nadd_add x y) z) (nadd_add (nadd_mul x z) (nadd_mul y z)))))))));
