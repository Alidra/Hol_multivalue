require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1247612 (m : El num) (p : El num) (n : El num) (q : El num) : Prf (= (∀ (λ d : El num, (∧ (⇒ (= (+ m n) (+ (+ p q) d)) (<= d (+ (dist ((@̦‚ num num) m p)) (dist ((@̦‚ num num) n q))))) (⇒ (= (+ p q) (+ (+ m n) d)) (<= d (+ (dist ((@̦‚ num num) m p)) (dist ((@̦‚ num num) n q)))))))) (<= (dist ((@̦‚ num num) (+ m n) (+ p q))) (+ (dist ((@̦‚ num num) m p)) (dist ((@̦‚ num num) n q)))));
