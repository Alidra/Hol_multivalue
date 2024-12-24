require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7539532 : Prf (∀ (λ n : El num, (∀ (λ c : El (fun num real), (= (∀ (λ x : El real, (= ((@sum num) (… (NUMERAL _0) n) (λ i : El num, (real_mul (c i) (real_pow x i)))) (real_of_num (NUMERAL _0))))) (∀ (λ i : El num, (⇒ ((@IN num) i (… (NUMERAL _0) n)) (= (c i) (real_of_num (NUMERAL _0)))))))))));
