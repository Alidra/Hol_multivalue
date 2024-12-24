require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6220935 [_123774] : Prf (∀ (λ op : El (fun _123774 (fun _123774 _123774)), (⇒ ((@monoidal _123774) op) (∀ (λ f : El (fun num _123774), (∀ (λ m : El num, (∀ (λ n : El num, (= ((@iterate _123774 num) op (… (* (NUMERAL (BIT0 (BIT1 _0))) m) (+ (* (NUMERAL (BIT0 (BIT1 _0))) n) (NUMERAL (BIT1 _0)))) f) ((@iterate _123774 num) op (… m n) (λ i : El num, (op (f (* (NUMERAL (BIT0 (BIT1 _0))) i)) (f (+ (* (NUMERAL (BIT0 (BIT1 _0))) i) (NUMERAL (BIT1 _0)))))))))))))))));
