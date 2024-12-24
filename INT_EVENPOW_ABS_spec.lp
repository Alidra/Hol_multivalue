require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2302004 : Prf (∀ (λ x : El int, (∀ (λ n : El num, (⇒ (EVEN n) (= (int_pow (int_abs x) n) (int_pow x n)))))));
