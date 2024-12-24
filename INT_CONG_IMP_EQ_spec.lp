require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2443203 : Prf (∀ (λ x : El int, (∀ (λ y : El int, (∀ (λ n : El int, (⇒ (∧ (int_lt (int_abs (int_sub x y)) n) ((@== int) x y (int_mod n))) (= x y))))))));
