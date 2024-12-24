require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1302075 : Prf (∀ (λ x : El nadd, (∀ (λ n : El num, (⇒ (¬ (= (dest_nadd x n) (NUMERAL _0))) (<= (dist ((@̦‚ num num) (* (dest_nadd x n) (nadd_rinv x n)) (* n n))) (dest_nadd x n)))))));
