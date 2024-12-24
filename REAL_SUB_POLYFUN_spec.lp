require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7393151 : Prf (∀ (λ a : El (fun num real), (∀ (λ x : El real, (∀ (λ y : El real, (∀ (λ n : El num, (⇒ (<= (NUMERAL (BIT1 _0)) n) (= (real_sub ((@sum num) (… (NUMERAL _0) n) (λ i : El num, (real_mul (a i) (real_pow x i)))) ((@sum num) (… (NUMERAL _0) n) (λ i : El num, (real_mul (a i) (real_pow y i))))) (real_mul (real_sub x y) ((@sum num) (… (NUMERAL _0) (- n (NUMERAL (BIT1 _0)))) (λ j : El num, (real_mul ((@sum num) (… (+ j (NUMERAL (BIT1 _0))) n) (λ i : El num, (real_mul (a i) (real_pow y (- (- i j) (NUMERAL (BIT1 _0))))))) (real_pow x j)))))))))))))));
