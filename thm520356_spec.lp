require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem520356 : Prf (= T (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (< (NUMERAL m) (NUMERAL n)) (< m n)))))) (∧ (= (< _0 _0) F) (∧ (∀ (λ n : El num, (= (< (BIT0 n) _0) F))) (∧ (∀ (λ n : El num, (= (< (BIT1 n) _0) F))) (∧ (∀ (λ n : El num, (= (< _0 (BIT0 n)) (< _0 n)))) (∧ (∀ (λ n : El num, (= (< _0 (BIT1 n)) T))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (< (BIT0 m) (BIT0 n)) (< m n)))))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (< (BIT0 m) (BIT1 n)) (<= m n)))))) (∧ (∀ (λ m : El num, (∀ (λ n : El num, (= (< (BIT1 m) (BIT0 n)) (< m n)))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (< (BIT1 m) (BIT1 n)) (< m n))))))))))))))));
