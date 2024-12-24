require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1105738 [_25569] : Prf (∧ (∀ (λ l : El (list _25569), (= ((@EL _25569) (NUMERAL _0) l) ((@HD _25569) l)))) (∀ (λ n : El num, (∀ (λ l : El (list _25569), (= ((@EL _25569) (SUC n) l) ((@EL _25569) n ((@TL _25569) l))))))));
