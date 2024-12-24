require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1518504 : Prf (∀ (λ w : El real, (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ z : El real, (⇒ (∧ (real_le w x) (real_lt y z)) (real_lt (real_add w y) (real_add x z)))))))))));
