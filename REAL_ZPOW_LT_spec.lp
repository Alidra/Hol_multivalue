require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3179557 : Prf (∀ (λ x : El real, (∀ (λ n : El int, (⇒ (real_lt (real_of_num (NUMERAL _0)) x) (real_lt (real_of_num (NUMERAL _0)) (real_zpow x n)))))));
