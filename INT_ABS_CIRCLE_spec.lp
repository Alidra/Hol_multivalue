require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2300381 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ h : El int, (⇒ (int_lt (int_abs h) (int_sub (int_abs y) (int_abs x))) (int_lt (int_abs (int_add x h)) (int_abs y)))))))));
