require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem170527 : Prf (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (¬ (= m (NUMERAL _0))) (= (DIV (* m n) m) n))))));
