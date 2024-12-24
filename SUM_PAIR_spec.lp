require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7226452 : Prf (∀ (λ f : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (= ((@sum num) (… (* (NUMERAL (BIT0 (BIT1 _0))) m) (+ (* (NUMERAL (BIT0 (BIT1 _0))) n) (NUMERAL (BIT1 _0)))) f) ((@sum num) (… m n) (λ i : El num, (real_add (f (* (NUMERAL (BIT0 (BIT1 _0))) i)) (f (+ (* (NUMERAL (BIT0 (BIT1 _0))) i) (NUMERAL (BIT1 _0))))))))))))));
