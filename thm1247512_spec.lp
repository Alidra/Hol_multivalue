require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247512 (n : El num) (d' : El num) (d : El num) : Prf (= (∀ (λ d'' : El num, (∧ (⇒ (= n (+ (+ (+ n d') d) d'')) (<= d (+ d' d''))) (⇒ (= (+ (+ n d') d) (+ n d'')) (<= d (+ d' d'')))))) (<= d (+ d' (dist ((@̦‚ num num) n (+ (+ n d') d))))));
