require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7226536 : Prf (∀ (λ x : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (= ((@sum num) (… m n) x) ((@COND real) (< n m) (real_of_num (NUMERAL _0)) ((@sum num) (… (NUMERAL _0) (- n m)) (λ i : El num, (x (- n i))))))))))));
