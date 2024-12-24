require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2308813 : Prf (∀ (λ x : El int, (∀ (λ n : El num, (= (int_pow (int_neg x) n) ((@COND int) (EVEN n) (int_pow x n) (int_neg (int_pow x n))))))));
