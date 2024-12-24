require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1248292 (d : El num) (d' : El num) (n : El num) (q : El num) : Prf (= (∀ (λ d'' : El num, (∧ (⇒ (= n (+ q d'')) (<= d (+ d' d''))) (⇒ (= q (+ n d'')) (<= d (+ d' d'')))))) (<= d (+ d' (dist ((@̦‚ num num) n q)))));
