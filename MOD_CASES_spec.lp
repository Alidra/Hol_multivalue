require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem177172 : Prf (∀ (λ n : El num, (∀ (λ p : El num, (⇒ (< n (* (NUMERAL (BIT0 (BIT1 _0))) p)) (= (MOD n p) ((@COND num) (< n p) n (- n p))))))));
