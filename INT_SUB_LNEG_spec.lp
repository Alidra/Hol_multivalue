require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2310253 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (= (int_sub (int_neg x) y) (int_neg (int_add x y)))))));
