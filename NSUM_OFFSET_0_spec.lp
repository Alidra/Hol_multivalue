require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7048892 : Prf (∀ (λ f : El (fun num num), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (<= m n) (= ((@nsum num) (… m n) f) ((@nsum num) (… (NUMERAL _0) (- n m)) (λ i : El num, (f (+ i m))))))))))));
