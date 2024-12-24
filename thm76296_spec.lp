require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem76296 : Prf (= BIT0 ((@ε (fun num num)) (λ fn : El (fun num num), (∧ (= (fn (NUMERAL _0)) (NUMERAL _0)) (∀ (λ n : El num, (= (fn (SUC n)) (SUC (SUC (fn n))))))))));
