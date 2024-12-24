require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7626934 [A N] : Prf (∀ (λ i : El num, (∃ (λ k : El num, (∧ (<= (NUMERAL (BIT1 _0)) k) (∧ (<= k ((@dimindex N) (@UNIV N))) (∀ (λ x : El (cart A N), (= ((@﹩ A N) x i) ((@﹩ A N) x k))))))))));
