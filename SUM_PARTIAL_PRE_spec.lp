require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7233425 : Prf (∀ (λ f : El (fun num real), (∀ (λ g : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (= ((@sum num) (… m n) (λ k : El num, (real_mul (f k) (real_sub (g k) (g (- k (NUMERAL (BIT1 _0)))))))) ((@COND real) (<= m n) (real_sub (real_sub (real_mul (f (+ n (NUMERAL (BIT1 _0)))) (g n)) (real_mul (f m) (g (- m (NUMERAL (BIT1 _0)))))) ((@sum num) (… m n) (λ k : El num, (real_mul (g k) (real_sub (f (+ k (NUMERAL (BIT1 _0)))) (f k)))))) (real_of_num (NUMERAL _0))))))))))));
