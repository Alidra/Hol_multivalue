require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1502113 : Prf (∀ (λ w : El real, (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (∧ (real_le w x) (real_le y z)) (real_le (real_add w y) (real_add x z)))))))))));
