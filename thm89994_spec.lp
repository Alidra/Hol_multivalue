require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem89994 : Prf (∧ (∀ (λ m : El num, (= (< m (NUMERAL _0)) F))) (∀ (λ m : El num, (∀ (λ n : El num, (= (< m (SUC n)) (∨ (= m n) (< m n))))))));
