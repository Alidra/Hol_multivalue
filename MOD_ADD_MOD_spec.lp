require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem209995 : Prf (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ n : El num, (= (MOD (+ (MOD a n) (MOD b n)) n) (MOD (+ a b) n))))))));
