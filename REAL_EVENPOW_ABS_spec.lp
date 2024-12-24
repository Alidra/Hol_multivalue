require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1669140 : Prf (∀ (λ x : El real, (∀ (λ n : El num, (⇒ (EVEN n) (= (real_pow (real_abs x) n) (real_pow x n)))))));
