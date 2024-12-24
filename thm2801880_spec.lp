require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2801880 : Prf (∀ (λ a : El int, (∀ (λ b : El int, (∧ (int_le (int_of_num (NUMERAL _0)) (int_gcd ((@̦‚ int int) a b))) (∧ (int_divides (int_gcd ((@̦‚ int int) a b)) a) (∧ (int_divides (int_gcd ((@̦‚ int int) a b)) b) (∃ (λ x : El int, (∃ (λ y : El int, (= (int_gcd ((@̦‚ int int) a b)) (int_add (int_mul a x) (int_mul b y))))))))))))));
