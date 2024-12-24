require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1280016 : Prf (∀ (λ x : El nadd, (∀ (λ y : El nadd, (∀ (λ z : El nadd, (⇒ (nadd_le y z) (nadd_le (nadd_mul x y) (nadd_mul x z)))))))));
