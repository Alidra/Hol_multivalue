require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem309993 [A] (a : El A) (f : El (fun A A)) : Prf (∃ (λ s : El (fun num A), (∧ (= (s (NUMERAL _0)) a) (∀ (λ n : El num, (= (s (SUC n)) (f (s n))))))));
