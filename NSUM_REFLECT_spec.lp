require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7052565 : Prf (∀ (λ x : El (fun num num), (∀ (λ m : El num, (∀ (λ n : El num, (= ((@nsum num) (… m n) x) ((@COND num) (< n m) (NUMERAL _0) ((@nsum num) (… (NUMERAL _0) (- n m)) (λ i : El num, (x (- n i))))))))))));
