require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3179362 : Prf (∀ (λ x : El real, (∀ (λ n : El int, (⇒ (real_le (real_of_num (NUMERAL _0)) x) (real_le (real_of_num (NUMERAL _0)) (real_zpow x n)))))));
