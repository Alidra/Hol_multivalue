require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7213834 : Prf (∀ (λ c : El real, (∀ (λ m : El num, (∀ (λ n : El num, (= ((@sum num) (… m n) (λ n' : El num, c)) (real_mul (real_of_num (- (+ n (NUMERAL (BIT1 _0))) m)) c))))))));
