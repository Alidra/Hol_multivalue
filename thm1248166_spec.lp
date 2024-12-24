require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1248166 (d : El num) (p : El num) (n : El num) (q : El num) : Prf (= (∀ (λ d' : El num, (∧ (⇒ (= (+ (+ p d) n) (+ (+ p q) d')) (<= d (+ d' (dist ((@̦‚ num num) n q))))) (⇒ (= (+ p q) (+ (+ (+ p d) n) d')) (<= d (+ d' (dist ((@̦‚ num num) n q)))))))) (<= d (+ (dist ((@̦‚ num num) (+ (+ p d) n) (+ p q))) (dist ((@̦‚ num num) n q)))));
