require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1248368 (m : El num) (d : El num) (n : El num) (q : El num) : Prf (= (∀ (λ d' : El num, (∧ (⇒ (= (+ m n) (+ (+ (+ m d) q) d')) (<= d (+ d' (dist ((@̦‚ num num) n q))))) (⇒ (= (+ (+ m d) q) (+ (+ m n) d')) (<= d (+ d' (dist ((@̦‚ num num) n q)))))))) (<= d (+ (dist ((@̦‚ num num) (+ m n) (+ (+ m d) q))) (dist ((@̦‚ num num) n q)))));
