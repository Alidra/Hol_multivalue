require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1279298 : Prf (∀ (λ x : El nadd, (∀ (λ x' : El nadd, (∀ (λ y : El nadd, (∀ (λ y' : El nadd, (⇒ (∧ (nadd_eq x x') (nadd_eq y y')) (nadd_eq (nadd_mul x y) (nadd_mul x' y')))))))))));
