require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2300843 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (int_le (int_abs (int_add x y)) (int_add (int_abs x) (int_abs y)))))));
