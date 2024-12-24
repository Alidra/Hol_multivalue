require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2303771 : Prf (∀ (λ w : El int, (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ z : El int, (⇒ (∧ (int_lt w x) (int_lt y z)) (int_lt (int_add w y) (int_add x z)))))))))));
