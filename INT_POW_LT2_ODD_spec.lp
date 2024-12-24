require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2308529 : Prf (∀ (λ n : El num, (∀ (λ x : El int, (∀ (λ y : El int, (⇒ (∧ (int_lt x y) (ODD n)) (int_lt (int_pow x n) (int_pow y n)))))))));
