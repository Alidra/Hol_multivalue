require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7552219 : Prf (∀ (λ n : El num, (∀ (λ c : El (fun num real), (∀ (λ k : El real, (= (∀ (λ x : El real, (= ((@sum num) (… (NUMERAL _0) n) (λ i : El num, (real_mul (c i) (real_pow x i)))) k))) (∧ (= (c (NUMERAL _0)) k) (∀ (λ i : El num, (⇒ ((@IN num) i (… (NUMERAL (BIT1 _0)) n)) (= (c i) (real_of_num (NUMERAL _0))))))))))))));
