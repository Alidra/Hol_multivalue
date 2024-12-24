require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1539586 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ d : El real, (⇒ (real_lt (real_abs (real_sub x y)) d) (real_lt y (real_add x d)))))))));
