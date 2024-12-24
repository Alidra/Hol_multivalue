require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2336267 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_le x y) (∀ (λ z : El int, (⇒ (int_lt y z) (int_lt x z)))))))));
