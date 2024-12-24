require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1248118 (m : El num) (p : El num) (n : El num) (q : El num) : Prf (= (∀ (λ d : El num, (∧ (⇒ (= m (+ p d)) (<= d (+ (dist ((@̦‚ num num) (+ m n) (+ p q))) (dist ((@̦‚ num num) n q))))) (⇒ (= p (+ m d)) (<= d (+ (dist ((@̦‚ num num) (+ m n) (+ p q))) (dist ((@̦‚ num num) n q)))))))) (<= (dist ((@̦‚ num num) m p)) (+ (dist ((@̦‚ num num) (+ m n) (+ p q))) (dist ((@̦‚ num num) n q)))));
