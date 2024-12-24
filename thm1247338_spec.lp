require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247338 (d : El num) (d' : El num) (n : El num) (p : El num) : Prf (= (∀ (λ d'' : El num, (∧ (⇒ (= n (+ p d'')) (<= d (+ d' d''))) (⇒ (= p (+ n d'')) (<= d (+ d' d'')))))) (<= d (+ d' (dist ((@̦‚ num num) n p)))));
