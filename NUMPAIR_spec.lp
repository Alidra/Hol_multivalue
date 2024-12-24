require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1046874 : Prf (∀ (λ x : El num, (∀ (λ y : El num, (= (NUMPAIR x y) (* (EXP (NUMERAL (BIT0 (BIT1 _0))) x) (+ (* (NUMERAL (BIT0 (BIT1 _0))) y) (NUMERAL (BIT1 _0)))))))));
