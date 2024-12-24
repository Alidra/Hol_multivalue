require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2708269 : Prf (∀ (λ a : El int, (∀ (λ b : El int, (∀ (λ m : El int, (∀ (λ n : El int, (⇒ ((@== int) a b (int_mod (int_mul m n))) ((@== int) (div a m) (div b m) (int_mod n)))))))))));
