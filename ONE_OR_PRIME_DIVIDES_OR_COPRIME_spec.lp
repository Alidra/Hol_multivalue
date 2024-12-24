require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3145207 : Prf (∀ (λ p : El num, (= (∨ (= p (NUMERAL (BIT1 _0))) (prime p)) (∀ (λ n : El num, (∨ (num_divides p n) (num_coprime ((@̦‚ num num) p n))))))));
