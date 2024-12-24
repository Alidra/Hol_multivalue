require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem86199 : Prf (∧ (∀ (λ m : El num, (= (EXP m (NUMERAL _0)) (NUMERAL (BIT1 _0))))) (∀ (λ m : El num, (∀ (λ n : El num, (= (EXP m (SUC n)) (* m (EXP m n))))))));
