require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247414 (d : El num) (d' : El num) (p : El num) : Prf (= (∀ (λ d'' : El num, (∧ (⇒ (= (+ (+ p d) d') (+ p d'')) (<= d (+ d' d''))) (⇒ (= p (+ (+ (+ p d) d') d'')) (<= d (+ d' d'')))))) (<= d (+ d' (dist ((@̦‚ num num) (+ (+ p d) d') p)))));
