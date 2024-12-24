require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1362863 : Prf (∀ (λ x : El real, (∀ (λ n : El num, (= (real_pow (real_neg x) n) ((@COND real) (EVEN n) (real_pow x n) (real_neg (real_pow x n))))))));
