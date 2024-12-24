require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2308119 : Prf (∀ (λ n : El num, (∀ (λ x : El int, (∀ (λ y : El int, (⇒ (ODD n) (= (= (int_pow x n) (int_pow y n)) (= x y)))))))));
