require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1274592 : Prf (∀ (λ x : El nadd, (∀ (λ y : El nadd, (∀ (λ z : El nadd, (nadd_eq (nadd_add x (nadd_add y z)) (nadd_add (nadd_add x y) z))))))));
