require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1544390 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ h : El real, (⇒ (real_lt (real_abs h) (real_sub (real_abs y) (real_abs x))) (real_lt (real_abs (real_add x h)) (real_abs y)))))))));
