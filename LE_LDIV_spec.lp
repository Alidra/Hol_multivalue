require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem191396 : Prf (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ n : El num, (⇒ (∧ (¬ (= a (NUMERAL _0))) (<= b (* a n))) (<= (DIV b a) n))))))));
