require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7047279 (f : El (fun num num)) : Prf (∧ (∀ (λ m : El num, (= ((@nsum num) (… m (NUMERAL _0)) f) ((@COND num) (= m (NUMERAL _0)) (f (NUMERAL _0)) (NUMERAL _0))))) (∀ (λ m : El num, (∀ (λ n : El num, (= ((@nsum num) (… m (SUC n)) f) ((@COND num) (<= m (SUC n)) (+ ((@nsum num) (… m n) f) (f (SUC n))) ((@nsum num) (… m n) f))))))));
