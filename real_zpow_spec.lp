require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3169164 : Prf (∀ (λ z : El real, (∀ (λ i : El int, (= (real_zpow z i) ((@COND real) (int_le (int_of_num (NUMERAL _0)) i) (real_pow z (num_of_int i)) (real_inv (real_pow z (num_of_int (int_neg i))))))))));
