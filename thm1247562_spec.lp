require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247562 (d' : El num) (m : El num) (d : El num) : Prf (= (∀ (λ d'' : El num, (∧ (⇒ (= (+ m d') (+ (+ m d) d'')) (<= d (+ d' d''))) (⇒ (= (+ m d) (+ (+ m d') d'')) (<= d (+ d' d'')))))) (<= d (+ d' (dist ((@̦‚ num num) (+ m d') (+ m d))))));
