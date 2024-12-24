require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem77241 : Prf (∧ (∀ (λ n : El num, (= (+ (NUMERAL _0) n) n))) (∀ (λ m : El num, (∀ (λ n : El num, (= (+ (SUC m) n) (SUC (+ m n))))))));
