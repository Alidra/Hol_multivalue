require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3148697 : Prf (∀ (λ p : El num, (= (prime p) (∀ (λ n : El num, (= (num_coprime ((@̦‚ num num) p n)) (¬ (num_divides p n))))))));
