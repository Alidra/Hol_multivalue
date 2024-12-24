require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2437408 : Prf (∀ (λ n : El int, (∀ (λ x : El int, (∀ (λ y : El int, (= (int_mod n x y) (int_divides n (int_sub x y)))))))));
