require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem151921 : Prf (∀ (λ x : El num, (∀ (λ y : El num, (∀ (λ n : El num, (⇒ (∧ (< x y) (¬ (= n (NUMERAL _0)))) (< (EXP x n) (EXP y n)))))))));
