require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6960934 [A] (b : El num) : Prf (∀ (λ s : El (fun A bool), (∀ (λ a : El A, (= ((@nsum A) s (λ x : El A, ((@COND num) (= x a) b (NUMERAL _0)))) ((@COND num) ((@IN A) a s) b (NUMERAL _0)))))));
