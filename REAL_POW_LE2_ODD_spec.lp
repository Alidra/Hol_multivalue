require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1661016 : Prf (∀ (λ n : El num, (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (∧ (real_le x y) (ODD n)) (real_le (real_pow x n) (real_pow y n)))))))));
