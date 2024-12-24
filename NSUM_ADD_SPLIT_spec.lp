require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7048325 : Prf (∀ (λ f : El (fun num num), (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (⇒ (<= m (+ n (NUMERAL (BIT1 _0)))) (= ((@nsum num) (… m (+ n p)) f) (+ ((@nsum num) (… m n) f) ((@nsum num) (… (+ n (NUMERAL (BIT1 _0))) (+ n p)) f))))))))))));
