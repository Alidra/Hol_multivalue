require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1663094 : Prf (∀ (λ n : El num, (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (ODD n) (= (real_lt (real_pow x n) (real_pow y n)) (real_lt x y)))))))));
