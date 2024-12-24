require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7539125 : Prf (∀ (λ n : El num, (∀ (λ c : El (fun num real), (= ((@FINITE real) ((@GSPEC real) (λ GEN_PVAR_348 : El real, (∃ (λ x : El real, ((@SETSPEC real) GEN_PVAR_348 (= ((@sum num) (… (NUMERAL _0) n) (λ i : El num, (real_mul (c i) (real_pow x i)))) (real_of_num (NUMERAL _0))) x)))))) (∃ (λ i : El num, (∧ ((@IN num) i (… (NUMERAL _0) n)) (¬ (= (c i) (real_of_num (NUMERAL _0))))))))))));
