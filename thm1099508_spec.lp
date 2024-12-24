require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1099508 [_25272] : Prf (∧ (∀ (λ x : El _25272, (= ((@REPLICATE _25272) (NUMERAL _0) x) (@NIL _25272)))) (∀ (λ n : El num, (∀ (λ x : El _25272, (= ((@REPLICATE _25272) (SUC n) x) ((@CONS _25272) x ((@REPLICATE _25272) n x))))))));
