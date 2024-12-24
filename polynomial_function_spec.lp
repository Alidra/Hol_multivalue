require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7553488 : Prf (∀ (λ p : El (fun real real), (= (polynomial_function p) (∃ (λ m : El num, (∃ (λ c : El (fun num real), (∀ (λ x : El real, (= (p x) ((@sum num) (… (NUMERAL _0) m) (λ i : El num, (real_mul (c i) (real_pow x i))))))))))))));
