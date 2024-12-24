require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2300256 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ d : El int, (⇒ (int_lt (int_abs (int_sub x y)) d) (int_lt y (int_add x d)))))))));
