require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem513386 : Prf (= (∀ (λ n : El num, (= (PRE (+ n n)) ((@COND num) (= n _0) _0 (SUC (+ (PRE n) (PRE n))))))) (∧ (∀ (λ n : El num, (= (PRE (NUMERAL n)) (NUMERAL (PRE n))))) (∧ (= (PRE _0) _0) (∧ (∀ (λ n : El num, (= (PRE (BIT0 n)) ((@COND num) (= n _0) _0 (BIT1 (PRE n)))))) (∀ (λ n : El num, (= (PRE (BIT1 n)) (BIT0 n))))))));
