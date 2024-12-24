require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El num) ≔ ((λ y0 : El num, (∧ (¬ (= y0 (NUMERAL (BIT1 _0)))) (∀ (λ y1 : El num, (⇒ (num_divides y1 y0) (∨ (= y1 (NUMERAL (BIT1 _0))) (= y1 y0))))))) x0);
symbol term0 ≔ (λ y0 : El num, (∧ (¬ (= y0 (NUMERAL (BIT1 _0)))) (∀ (λ y1 : El num, (⇒ (num_divides y1 y0) (∨ (= y1 (NUMERAL (BIT1 _0))) (= y1 y0)))))));
symbol term3 ≔ (∀ (λ y0 : El num, (= (prime y0) (∧ (¬ (= y0 (NUMERAL (BIT1 _0)))) (∀ (λ y1 : El num, (⇒ (num_divides y1 y0) (∨ (= y1 (NUMERAL (BIT1 _0))) (= y1 y0)))))))));
symbol term2 (x0: El num) ≔ (∧ (¬ (= x0 (NUMERAL (BIT1 _0)))) (∀ (λ y0 : El num, (⇒ (num_divides y0 x0) (∨ (= y0 (NUMERAL (BIT1 _0))) (= y0 x0))))));
symbol term4 (x0: El num) ≔ ((λ y0 : El num, (= (prime y0) (∧ (¬ (= y0 (NUMERAL (BIT1 _0)))) (∀ (λ y1 : El num, (⇒ (num_divides y1 y0) (∨ (= y1 (NUMERAL (BIT1 _0))) (= y1 y0)))))))) x0);
