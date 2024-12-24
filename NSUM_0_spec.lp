require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6931080 [A] : Prf (∀ (λ s : El (fun A bool), (= ((@nsum A) s (λ n : El A, (NUMERAL _0))) (NUMERAL _0))));
