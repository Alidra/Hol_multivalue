require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem196344 (m : El num) : Prf (∀ (λ n : El num, (⇒ (¬ (= n (NUMERAL _0))) (= (= (DIV m n) (NUMERAL _0)) (< m n)))));
