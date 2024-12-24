require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6192133 [_123419] (f : El (fun num _123419)) : Prf (∀ (λ op : El (fun _123419 (fun _123419 _123419)), (⇒ ((@monoidal _123419) op) (∧ (∀ (λ m : El num, (= ((@iterate _123419 num) op (… m (NUMERAL _0)) f) ((@COND _123419) (= m (NUMERAL _0)) (f (NUMERAL _0)) ((@neutral _123419) op))))) (∀ (λ m : El num, (∀ (λ n : El num, (= ((@iterate _123419 num) op (… m (SUC n)) f) ((@COND _123419) (<= m (SUC n)) (op ((@iterate _123419 num) op (… m n) f) (f (SUC n))) ((@iterate _123419 num) op (… m n) f)))))))))));
