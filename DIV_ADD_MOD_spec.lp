require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem210482 : Prf (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ n : El num, (⇒ (¬ (= n (NUMERAL _0))) (= (= (MOD (+ a b) n) (+ (MOD a n) (MOD b n))) (= (DIV (+ a b) n) (+ (DIV a n) (DIV b n)))))))))));
