require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7044408 : Prf (∀ (λ c : El num, (∀ (λ m : El num, (∀ (λ n : El num, (= ((@nsum num) (… m n) (λ n' : El num, c)) (* (- (+ n (NUMERAL (BIT1 _0))) m) c))))))));
