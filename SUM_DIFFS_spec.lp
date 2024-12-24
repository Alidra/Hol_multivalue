require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7235163 (f : El (fun num real)) : Prf (∀ (λ m : El num, (∀ (λ n : El num, (= ((@sum num) (… m n) (λ k : El num, (real_sub (f k) (f (+ k (NUMERAL (BIT1 _0))))))) ((@COND real) (<= m n) (real_sub (f m) (f (+ n (NUMERAL (BIT1 _0))))) (real_of_num (NUMERAL _0))))))));
