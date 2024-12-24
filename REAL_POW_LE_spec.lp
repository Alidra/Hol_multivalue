require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1582434 : Prf (∀ (λ x : El real, (∀ (λ n : El num, (⇒ (real_le (real_of_num (NUMERAL _0)) x) (real_le (real_of_num (NUMERAL _0)) (real_pow x n)))))));
