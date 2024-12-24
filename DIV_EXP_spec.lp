require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem238173 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (⇒ (¬ (= m (NUMERAL _0))) (= (DIV (EXP m n) (EXP m p)) ((@COND num) (<= p n) (EXP m (- n p)) ((@COND num) (= m (NUMERAL (BIT1 _0))) (NUMERAL (BIT1 _0)) (NUMERAL _0)))))))))));
