require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2304006 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (⇒ (int_lt x y) (int_le x y))))));
