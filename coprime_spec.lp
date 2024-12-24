require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3137141 (a : El num) (b : El num) : Prf (= (num_coprime ((@̦‚ num num) a b)) (∀ (λ d : El num, (⇒ (∧ (num_divides d a) (num_divides d b)) (= d (NUMERAL (BIT1 _0)))))));
